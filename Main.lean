import Book
import VersoManual

open Verso.Genre.Manual

def main :=
  manualMain (%doc Book) (config := config)
where
  config := {
    emitTeX := false
    emitHtmlSingle := .no
    sourceLink := some "https://github.com/cboone/shannon-entropy"
    issueLink := some "https://github.com/cboone/shannon-entropy/issues"
  }
