import VersoManual
import VersoBlueprint.PreviewManifest
import SYK.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc SYK.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
