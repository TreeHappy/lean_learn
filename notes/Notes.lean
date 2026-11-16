import VersoManual

import Notes.Home
import Notes.Lean
import Notes.Lake
import Notes.Mathlib
import Notes.Reservoir
import Notes.LeanNvim
import Notes.AstroNvim
import Notes.Verso
import Notes.Project
import Notes.Exercises
import Notes.Index

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Brane: A Lean Research Notebook" =>
%%%
shortTitle := "Brane Notes"
authors := ["Brane"]
date := "2026-11-14"
%%%

This manual documents the Brane workspace: the Lean toolchain, the editor setup, and the conventions used to keep code and notes connected.

Try the [3D geodesic sandbox](../){index}[geodesic sandbox] that goes with these notes — an interactive shooting-method demo built on `Brane.Shooting`.

It is a book-like document built with Verso's Manual genre, so chapters, cross-references, the glossary, and the index are all checked by Lean.

{include 0 Notes.Home}

{include 0 Notes.Lean}

{include 0 Notes.Lake}

{include 0 Notes.Mathlib}

{include 0 Notes.Reservoir}

{include 0 Notes.LeanNvim}

{include 0 Notes.AstroNvim}

{include 0 Notes.Verso}

{include 0 Notes.Project}

{include 0 Notes.Exercises}

{include 0 Notes.Index}
