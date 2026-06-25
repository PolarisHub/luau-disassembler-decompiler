local Debris = game:GetService("Debris")
local TweenService = game:GetService("TweenService")

local M = {}

function M:Add(part)
    Debris:AddItem(part, 1)
    TweenService:Create(part, TweenInfo.new(1), { Transparency = 1 }):Play()
end

return M
