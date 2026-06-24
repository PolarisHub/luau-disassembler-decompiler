local function shout(s)
	local upper = s:upper()
	local rep = upper:rep(2)
	return rep:len()
end
return shout
