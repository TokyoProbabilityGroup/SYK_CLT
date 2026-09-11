import VersoManual
import VersoBlueprint.PreviewManifest
import SYK.Blueprint

open Verso Doc
open Verso.Genre Manual

private def outputDirectory : List String → System.FilePath
  | "--output" :: path :: _ => path
  | _ :: args => outputDirectory args
  | [] => "_out"

private def windowsSearchAssetDirectory (output : System.FilePath) : System.FilePath :=
  output.parent.getD "." / "static-web" / "search"

private def prepareWindowsSearchAssets (output : System.FilePath) : IO Unit := do
  if System.Platform.isWindows then
    -- Verso 4.32 retains the relative source prefix in bundled search-asset names on Windows.
    -- Creating its normalized destination lets rendering finish; the files are copied below.
    IO.FS.createDirAll (windowsSearchAssetDirectory output)

private def finishWindowsSearchAssets (output : System.FilePath) : IO Unit := do
  if System.Platform.isWindows then
    let source := windowsSearchAssetDirectory output
    let destination := output / "html-multi" / "-verso-search"
    IO.FS.createDirAll destination
    for entry in (← source.readDir) do
      if (← entry.path.metadata).type == .file then
        IO.FS.writeBinFile (destination / entry.fileName) (← IO.FS.readBinFile entry.path)

def main (args : List String) : IO UInt32 := do
  let output := outputDirectory args
  prepareWindowsSearchAssets output
  let result ← Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc SYK.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
  if result == 0 then
    finishWindowsSearchAssets output
  return result
