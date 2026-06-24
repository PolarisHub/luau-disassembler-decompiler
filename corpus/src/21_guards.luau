-- Short-circuit guard chains: `if not (a and b ...) then <terminator> end`.
-- These compile to a run of conditional jumps converging on a return/break block,
-- which the structurer must recover as a single combined condition.

local function twoAnd(a, b, x)
	if not (a and b) then
		return nil
	end
	return x
end

local function threeAnd(a, b, c, x)
	if not (a and b and c) then
		return "bad"
	end
	return x
end

local function guardThenWork(t, key, val)
	if not (t and key) then
		return
	end
	t[key] = val
	return t
end

local function guardInLoop(items)
	local total = 0
	for _, it in ipairs(items) do
		if not (it and it.amount) then
			break
		end
		total = total + it.amount
	end
	return total
end

-- Effectful-guard chain: the right-hand side of `and` is a call whose result is tested
-- immediately. The compiler emits it as two conditional jumps with intervening code
-- between them, which the structurer must rebuild as flat sequential guards.
local function guardWithCall(panel, name)
	if not (panel and panel:FindFirstChild(name)) then
		return false
	end
	return true
end

return { twoAnd, threeAnd, guardThenWork, guardInLoop, guardWithCall }
