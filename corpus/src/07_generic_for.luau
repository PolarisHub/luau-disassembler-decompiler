local function dump(t)
	local out = {}
	for i, v in ipairs(t) do
		out[i] = v
	end
	for k, v in pairs(t) do
		out[k] = v
	end
	return out
end
return dump
