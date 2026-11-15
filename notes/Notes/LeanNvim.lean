import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "lean.nvim" =>
%%%
tag := "lean-nvim"
htmlSplit := .never
%%%

[lean.nvim](https://github.com/Julian/lean.nvim){index}[lean.nvim] is the Neovim plugin that connects the editor to Lean's language server, `leanls`.
It provides diagnostics, interactive hover information, the infoview, goal displays, Unicode abbreviations, and commands for restarting or inspecting the server.

This chapter records both the configuration and the two problems that made the plugin appear broken at first.

# How the server starts
%%%
tag := "lean-nvim-server"
%%%

`lean.nvim` starts `leanls` through Neovim's built-in LSP client.
Inside a Lake package it runs:

```
lake serve -- <project-root>
```

If `lake` cannot be found, the server never starts and no features appear, even though the plugin itself is installed correctly.
Neovim does not read `~/.bashrc`, so a `PATH` entry that works in a terminal may be absent from Neovim's environment.

The check is:

```
:lua =vim.fn.exepath("lake")
```

An empty result means Neovim cannot see the elan toolchain.

# Fixing PATH
%%%
tag := "lean-nvim-path"
%%%

Elan installs `lake` and `lean` into `~/.elan/bin`.
That directory is now prepended to both shells and Neovim.

In `~/.bashrc`:

```
export PATH="$HOME/.elan/bin:$PATH"
```

In `~/.config/nvim/init.lua`, before Lazy is set up:

```
local elan_bin = vim.fs.joinpath(vim.env.HOME or "", ".elan", "bin")
if vim.uv.fs_stat(elan_bin) then vim.env.PATH = elan_bin .. ":" .. vim.env.PATH end
```

Setting `vim.env.PATH` is the important part: it changes the environment of the editor process, which is what the LSP client inherits.

# The configuration trap
%%%
tag := "lean-nvim-config"
%%%

AstroNvim's community pack configured the plugin with Lazy's `opts` table.
That convention assumes a plugin exposes a `setup` function.
`lean.nvim` does not; it reads `vim.g.lean_config` instead.
As a result the pack's settings, including `mappings = true`, were silently ignored.

The repository now uses a dedicated plugin file, `~/.config/nvim/lua/plugins/lean.lua`:

```
return {
  {
    "Julian/lean.nvim",
    ft = { "lean" },
    init = function()
      vim.g.lean_config = vim.tbl_deep_extend("force", vim.g.lean_config or {}, {
        mappings = true,
        infoview = { autoopen = true, width = 0.35 },
      })
    end,
  },
}
```

The `init` function runs before the plugin loads, so the configuration exists when `lean.nvim` reads it.
The `astrocommunity.pack.lean` import was removed from `lua/community.lua` to avoid configuring the plugin twice.

# Mappings
%%%
tag := "lean-nvim-mappings"
%%%

With `mappings = true`, the local leader is `,` in AstroNvim's default setup.

: `,i`

  Toggle the infoview.

: `,p`

  Pause or resume pin updates.

: `,x`

  Add an infoview pin at the cursor.

: `,c`

  Clear all pins.

: `,dx` and `,dc`

  Set and clear a diff pin.

: `,dd` and `,dt`

  Toggle auto-diff mode, with and without clearing existing pins.

: `,w` and `,W`

  Enable and disable infoview widgets.

: `,v`

  Change infoview view options.

: `,s`

  Accept the first suggestion shown in the infoview.

: `,\`

  Show how to type the Unicode character under the cursor.

: `,r`

  Restart the Lean server for the current file.

: `K`

  Show interactive Lean hover information.

The usual LSP mappings for definitions, references, renames, and diagnostics are supplied globally by AstroLSP, so they are available in Lean buffers without extra configuration.

# Commands
%%%
tag := "lean-nvim-commands"
%%%

: `:LeanGoal`

  Show the main goal in a popup.

: `:LeanTermGoal`

  Show the expected type at the cursor.

: `:LeanLineDiagnostics`

  Show diagnostics for the current line.

: `:LeanRestartFile`

  Restart the server for this file.

: `:LeanRefreshFileDependencies`

  Refresh dependencies and restart.

# Troubleshooting
%%%
tag := "lean-nvim-troubleshooting"
%%%

 * `:lua =vim.lsp.get_clients()` should contain a client named `leanls` in a Lean buffer.
 * `:messages` shows server startup errors and Lean diagnostics.
 * If the infoview is empty, check that the cursor is inside a proof and that the file has no parse errors.
 * A watchdog message mentioning `/etc/localtime` is cosmetic in this container and does not prevent the server from attaching.

For the surrounding editor configuration, see {ref "astro-nvim"}[AstroNvim].
