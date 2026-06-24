local function build(x)
	local arr = { 10, 20, 30, 40 }
	local hash = { name = "luau", value = x, active = true }
	local mixed = { 1, 2, key = "v", 3 }
	hash.extra = arr[1]
	return arr, hash, mixed
end
return build
