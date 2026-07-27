local null_ls = require("null-ls")

local function get_qids(prms)
  local ts = vim.treesitter
  local query = ts.query.parse("agda", "(qid) @qid")
  local buffer = prms.bufnr
  local buf_highlighter = require('vim.treesitter.highlighter')
      .active[buffer]
  local line_count = vim.api.nvim_buf_line_count(buffer)

  local qidst = {}

  buf_highlighter.tree:for_each_tree(function(tstree, tree)
    if tree:lang() ~= 'agda' then
      return
    end

    local root = tstree:root()
    local iter = query:iter_captures(root, buffer, 0, line_count + 1)

    for _, node, _ in iter do
      local text = ts.get_node_text(node, buffer)
      qidst[text] = true
    end
  end)

  local items = {}

  for qid, _ in pairs(qidst) do
    table.insert(items, {
      label = qid,
      insertText = qid
    })
  end

  return {
    {
      items = items,
      isIncomplete = true,
    },
  }
end

local agda_compl = {
  name = "agda_compl",
  filetypes = { "agda" },
  method = { null_ls.methods.COMPLETION },
  generator = {
    fn = get_qids,
  },
  id = 1,
}

null_ls.register({ agda_compl })
