import VersoManual
import Book.Introduction
import Book.Bibliography

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Shannon 1948: A Formalization Companion" =>
%%%
tag := "shannon-1948-formalization-companion"
shortContextTitle := "Shannon Companion"
%%%

This companion book explains the Lean 4 formalization in this repository alongside Shannon's 1948 paper.
It is structured as a Manual so later phases can add chapters, internal cross-references, and bibliography material without changing the publication model.

{include 0 Book.Introduction}

{include 0 Book.Bibliography}
