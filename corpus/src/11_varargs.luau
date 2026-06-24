local function variadic(...)
	local first = ...
	local packed = { ... }
	local n = select("#", ...)
	return first, packed, n
end
return variadic
