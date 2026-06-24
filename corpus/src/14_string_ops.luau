local function work(s, n)
	local sub = string.sub(s, 1, n)
	local len = string.len(s)
	local floor = math.floor(n)
	local maxv = math.max(n, len)
	return sub, len, floor, maxv
end
return work
