import VersoManual
import VersoBlueprint.PreviewManifest
import SakAIDocs.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc SakAIDocs.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
