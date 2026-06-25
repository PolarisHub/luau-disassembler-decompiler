local M = {}

function M:GetPoint(i)
    return i
end

function M:GetAllPoints()
    local result = {}
    for i = 1, #self.Points do
        table.insert(result, self:GetPoint(i))
    end
    return result
end

return M
