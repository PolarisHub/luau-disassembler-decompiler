local function calc(x, y)
	local add = x + y
	local sub = x - y
	local mul = x * y
	local div = x / y
	local idiv = x // y
	local mod = x % y
	local pow = x ^ y
	local neg = -x
	local len = #y
	local cat = x .. y
	return add, sub, mul, div, idiv, mod, pow, neg, len, cat
end
return calc
