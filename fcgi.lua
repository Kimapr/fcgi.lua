#!/usr/bin/env lua
--[[--

Lua FastCGI library based on cqueues.

Usage:
fcgi.serve(sock: (cqueues stream socket),handlers: {
	request = function(req: {
		role = "responder" | "authorizer" | "filter",
		env = {...}, -- CGI variables
		stdin = (file),
		stdout = (file),
		stderr = (file),
		-- only if role == "filter"
		-- data = (file)
	}),

	-- catch errors from the request handler
	err = function(req,err),

	-- called when a request is aborted
	abort = function(req,reason: "protocol error" | "connection closed" | "abort request")
})


Copyright (C)2022 Kimapr

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject
to the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY
KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE
WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
--]]--

local _
local lib={}
local async=require"cqueues"
local socket=require"cqueues.socket"
local condition=require"cqueues.condition"
--local print=function()end -- disable debug

local FCGI={
	HEADER_LEN=8,

	VERSION=1,

	-- record types
	BEGIN_REQUEST=1,
	ABORT_REQUEST=2,
	END_REQUEST=3,
	PARAMS=4,
	STDIN=5,
	STDOUT=6,
	STDERR=7,
	DATA=8,
	GET_VALUES=9,
	GET_VALUES_RESULT=10,
	UNKNOWN_TYPE=11,
	MAXTYPE=11,

	NULL_REQUEST_ID=0,

	KEEP_CONN=1,
	
	-- roles
	RESPONDER=1,
	AUTHORIZER=2,
	FILTER=3,

	-- protocolStatus
	REQUEST_COMPLETE=0,
	CANT_MPX_CONN=1,
	OVERLOADED=2,
	UNKNOWN_ROLE=3,

	MAX_CONNS="FCGI_MAX_CONNS",
	MAX_REQS="FCGI_MAX_REQS",
	MPXS_CONNS="FCGI_MPXS_CONNS",
}
local function r(n)
	return ("\0"):rep(n or 1)
end
local record_fmt=">B B I2 I2 B c1"
function FCGI.Record(t,reqid,content)
	assert(#content<2^16,"too big")
	return record_fmt:pack(FCGI.VERSION,t,reqid,#content,0,r())..content
end
local begin_req_fmt=">I2 B c5"
local end_req_fmt=">I4 B c3"
function FCGI.EndRequestBody(s_app,s_proto)
	return end_req_fmt:pack(s_app,s_proto,r(3))
end
local unknown_type_fmt=">B c7"
function FCGI.UnknownTypeBody(t)
	return unknown_type_fmt:pack(t)
end
local function encnvpl(l)
	if l<127 then
		return ("B"):pack(l)
	end
	if l<2^31-1 then return nil end
	return (">I4"):pack(2^31+l)
end
function FCGI.NameValuePair(n,v)
	local ln,lv=encnvpl(#n),encnvpl(#v)
	if not ln or not lv then return nil end
	return encnvpl(n)..encnvpl(v)..n..v
end

local function readRecord(con)
	local rech = con:read(FCGI.HEADER_LEN)
	if not rech or #rech~=FCGI.HEADER_LEN then return nil,"header read fail" end
	local ver,t,reqid,clen,plen = record_fmt:unpack(rech)
	local content=""
	if clen+plen>0 then
		content = con:read(clen+plen):sub(1,clen)
	end
	if not content or #content~=clen then return nil,"content read fail" end
	if ver~=FCGI.VERSION then return nil,"unsupported version" end
	return t,reqid,content
end
local function strReader_read(self,n)
	assert(type(n)=="number")
	if self.__c>#self.__str then return nil end
	local ss=self.__str:sub(self.__c,self.__c+n-1)
	self.__c=self.__c+n
	return ss
end
local function strReader(str)
	local file = {__str=str,__c=1,read=strReader_read}
	return file
end
local function readNVPL(con)
	local p1=con:read(1)
	if not p1 or #p1~=1 then return nil end
	local b=("B"):unpack(p1)
	if b>>7==1 then
		local p2=con:read(3)
		if not p2 or #p2~=3 then return nil end
		p1=p1..p2
		b=(">I4"):unpack(p1) & (2^31-1)
	end
	return b
end
local function readNVP(con)
	local nl,vl=readNVPL(con),readNVPL(con)
	if not nl or not vl then return nil,"name-value header read fail" end
	local dat=con:read(nl+vl)
	if not dat or #dat~=nl+vl then return nil,"name-value read fail" end
	return dat:sub(1,nl),dat:sub(nl+1,nl+vl)
end
local function readNVPs(con)
	local t={}
	local errs=0
	while con:read(0) do
		local n,v=readNVP(con)
		if n then
			t[n]=v
		else
			break
		end
	end
	return t
end

local function protocolError(state)
	io.stderr:write("Protocol error!\n")
end

local function scon_write(state,t,reqid,str)
	table.insert(state.sendqueue,FCGI.Record(t,reqid,str))
	state.writecond:signal()
end

local function reqstream_wrf(state,t,reqid)
	return function(str)
		scon_write(state,t,reqid,str)
	end
end

local function aquirelock(t,f,...)
	local field="__lock_"..f
	local cond=t[field.."_cond"]
	while t[field] do
		cond:wait()
	end
	t[field]=true
	return function()
		t[field]=nil
		cond:signal()
	end
end

local reqstream_mt={}
local reqstream_rmt={__index=reqstream_mt}

local function reqstream(wrf)
	return setmetatable({
		__rs={
			done=false,
			closed=false,
			w=wrf,
			data={},
			datal=0,
			buf={},
			bufl=0,
			__c=1,
			__lock_read_cond=condition.new(),
			__lock_write_cond=condition.new(),
			cond=condition.new(),
		},
		__push = not wrf and function(self,str)
			self = self.__rs
			if str then
				table.insert(self.data,str)
				self.datal=self.datal+#str
			else
				self.done=true
			end
			self.cond:signal()
		end or nil,
	},reqstream_rmt)
end

local function check_closed(rs)
	assert(not rs.closed,"attempt to use a closed file")
end
local function lockfn(fn,t)
	return function(self,...)
		local unlock=aquirelock(self.__rs,t)
		local ret=table.pack(fn(self,...))
		unlock()
		return table.unpack(ret,1,ret.n)
	end
end
function reqstream_mt:read(f,...)
	local rs=self.__rs
	check_closed(rs)
	if rs.w then return nil end
	if not f then f="l" end
	local fmts={f,...}
	local rets={}
	for n=1,#fmts do
		local f=fmts[n]
		if not f then error("invalid format") end
		if type(f)=="string" then
			if f:sub(1,1)=="*" then f=f:sub(2,2) else f=f:sub(1,1) end
			if f:lower()~="l" and f~="a" then error("invalid format") end
		end
		if rs.done and rs.__c > rs.datal then
			return table.unpack(rets,n)
		end
		if type(f)=="number" then
			while not rs.done and (rs.datal)<rs.__c+f-1 do
				rs.cond:wait()
				check_closed(rs)
			end
			if f>0 then
				local dstr=#rs.data
				local ll=0;
				for k,v in ipairs(rs.data) do
					ll=ll+#v
					if (ll)>=rs.__c+f-1 then
						dstr=k
						break
					end
				end
				rets[n]=table.concat(rs.data,nil,1,dstr):sub(rs.__c,rs.__c+f-1)
			else
				rets[n]=""
			end
			rs.__c=rs.__c+f
		elseif f:lower()=="l" then
			local dstr
			while not dstr and not rs.done do
				for k,v in ipairs(rs.data) do
					if v:find("[\n\r]") then
						dstr=k
						break
					end
				end
				rs.cond:wait()
				check_closed(rs)
			end
			dstr=table.concat(rs.data,nil,1,dstr or #rs.data)
			local _n=dstr:find("[\n\r]")
			local i=rs.__c
			local j=math.min(_n or math.huge, #dstr)
			local j2=j
			if dstr:sub(j,j)=="\r" and dstr:sub(j+1,j+1)=="\n" then
				j2=j+1
			end
			j=j-1
			rs.__c=rs.__c+(j2-i+1)
			rets[n]=dstr:sub(i,f=="L" and j2 or j)
		elseif f=="a" then
			while not rs.done do
				rs.cond:wait()
				check_closed(rs)
			end
			local dstr=table.concat(rs.data)
			rs.__c=rs.__c+#dstr
			rets[n]=dstr:sub(rs.__c,rs.datal)
		end
		while rs.data[1] and #(rs.data[1]) < rs.__c do
			rs.__c=rs.__c-#rs.data
			table.remove(rs.data,1)
			rs.datal=rs.datal-1
		end
	end
	return table.unpack(rets,1,#fmts)
end
function reqstream_mt:write(...)
	local rs=self.__rs
	check_closed(rs)
	if not rs.w then return nil end
	str=table.concat{...}
	if rs.bufl+#str>2^16-1 then
		local ss=str:sub(1,2^16-1-#str)
		if not self:write(str:sub(1,ss)) then return nil end
		self:flush()
		return self:write(str:sub(ss+1,-1))
	end
	table.insert(rs.buf,str)
	rs.bufl=rs.bufl+#str
	return self
end
reqstream_mt.read=lockfn(reqstream_mt.read,"read")
reqstream_mt.write=lockfn(reqstream_mt.write,"write")
function reqstream_mt:flush()
	local rs=self.__rs
	check_closed(rs)
	if not rs.w then return end
	if rs.bufl>0 then
		local str=table.concat(rs.buf)
		rs.buf,rs.bufl={},0
		rs.w(str)
	end
end
function reqstream_mt:close()
	local rs=self.__rs
	local ru,wu=aquirelock(rs,"read"),aquirelock(rs,"write")
	assert(not rs.closed,"attempt to use a closed file")
	self:flush()
	if rs.w then
		rs.w("")
	end
	rs.closed=true
	ru()wu()
end
function reqstream_mt:isclosed()
	return self.__rs.closed
end

local streamrecs={
	[FCGI.STDIN]=true,
	[FCGI.DATA]="data",
	[FCGI.PARAMS]="param"
}

local function tpcall(fn,...)
	local args=table.pack(...)
	return xpcall(function()
		return fn(table.unpack(args,1,args.n))
	end,debug.traceback or function(a)return a;end)
end

local packhandlers={}
local rolenames={
	[FCGI.RESPONDER]="responder",
	[FCGI.AUTHORIZER]="authorizer",
	[FCGI.FILTER]="filter"
}
packhandlers[FCGI.BEGIN_REQUEST]=function(state,t,reqid,content)
	local reqs,con,que = state.reqs, state.con, state.que
	local role,flags=begin_req_fmt:unpack(content)
	local keep_conn=(flags & FCGI.KEEP_CONN) ~= 0
	local req
	req={
		reqid=reqid,
		role=role,
		keep_conn=keep_conn,
		handling=false,
		param=reqstream(),
		stdin=reqstream(),
		data=role==FCGI.FILTER and newstream(),
		stdout=reqstream(reqstream_wrf(state,FCGI.STDOUT,reqid)),
		stderr=reqstream(reqstream_wrf(state,FCGI.STDERR,reqid)),
		abort=function(reason)
			req.aborted=true
			if req.handling then
				state.abort(ureq,reason)
			end
			for k,v in ipairs{param,stdin,stdout,stderr} do
				if not v:isclosed() then
					v:__push()
				end
			end
		end,
	}
	req.ureq={
		role=rolenames[role],
		stdin=req.stdin,
		data=role==FCGI.FILTER and req.data,
		stdout=req.stdout,
		stderr=req.stderr
	}
	local ureq=req.ureq
	reqs[reqid]=req
	local function die()
		ureq.stdin:close()
		ureq.stdout:close()
		ureq.stderr:close()
		if ureq.data then
			ureq.data:close()
		end
	end
	que:wrap(function()
		ureq.env=readNVPs(req.param)
		que:wrap(function()
			req.handling=true
			local ok,err,err2=tpcall(state.handler,ureq)
			ureq.stdout:flush()
			ureq.stderr:flush()
			local status = tonumber(err) or (err and 0 or 1)
			local protos = FCGI.REQUEST_COMPLETE
			local succ = true
			if not ok then
				status = 1
				if state.err then
					state.err(ureq,err)
				else
					error(err)
				end
			elseif not err then
				succ = false
				status = 1
				if err2=="unknown role" then
					protos=FCGI.UNKNOWN_ROLE
				elseif err=="overloaded" then
					protos=FCGI.OVERLOADED
				end
			end
			if succ then
				die()
			end
			scon_write(state,FCGI.END_REQUEST,reqid,FCGI.EndRequestBody(status,protos))
			req.handling=false
			reqs[reqid]=nil
			if succ and not req.keep_conn then
				table.insert(state.sendqueue,false)
			end
		end)
	end)
end

packhandlers[FCGI.ABORT_REQUEST]=function(state,t,reqid,content)
	local reqs = state.reqs
	if reqs[reqid] then
		reqs[reqid].abort("abort request")
	end
end

local vars={
	[FCGI.MPXS_CONNS]="1"
}

packhandlers[FCGI.GET_VALUES]=function(state,t,reqid,content)
	local names=readNVPs(strReader(content))
	local res={}
	for k,v in pairs(vars) do
		if names[k] then
			table.insert(res,FCGI.NameValuePair(k,v))
		end
	end
	scons_write(state,FCGI.GET_VALUES_RESULT,reqid,content)
end

local function stream_packhandler(state,t,reqid,content)
	local reqs,con,que = state.reqs, state.con, state.que
	local cc=(reqs[reqid] or {})[streamrecs[t]]
	if not cc then return end
	cc:__push(#content>0 and content or nil)
end

for k,v in pairs(streamrecs) do
	packhandlers[k]=stream_packhandler
end

local function handleClient(state,con)
	state = setmetatable({
		reqs = {},
		sendqueue={},
		con=con,
		writecond=condition.new()
	},{__index = state})
	local reqs = state.reqs
	local con = state.con
	local que = state.que
	local reading=false
	local reading_cond=condition.new()
	que:wrap(function()
		while state.con do
			state.writecond:wait()
			if not state.con then return end
			while #state.sendqueue>0 do
				local v=table.remove(state.sendqueue,1)
				if v==false then
					con:flush()
					con:shutdown("rw")
					while reading do reading_cond:wait() end
					con:close()
					state.con=nil;
					return
				end
				con:write(v)
				if con:eof("w") then
					for k,v in pairs(reqs) do
						v.abort("connection closed")
					end
					return
				end
			end
			con:flush()
		end
	end)
	while state.con and not con:eof("r") do
		reading=true
		local ok,t,reqid,content=pcall(readRecord,con)
		if not ok then
			state.con=nil
			reading=nil
			state.writecond:signal()
			reading_cond:signal()
			for k,v in pairs(reqs) do
				v.abort("protocol error")
			end
			print("connection error")
			return
		end
		if not t then reading=false;reading_cond:signal() return end
		(packhandlers[t] or function()
			scon_write(state,FCGI.UNKNOWN_TYPE,reqid,FCGI.UnknownTypeBody(t))
		end)(state,t,reqid,content);
		reading=false
		reading_cond:signal()
	end
end

function lib.serve(sock,hands)
	local que=async.new()
	local state = {
		que=que,
		handler=hands.request or error("handler func required"),
		abort=hands.abort or function()end,
		err=hands.err,
	}
	que:wrap(function()
		for con in sock:clients() do
			con:setmode("bf","bf")
			que:wrap(function()
				handleClient(state,con)
			end)
		end
	end)
	assert(que:loop())
end

return lib
