module

import all SYK.Main
public meta import Lean.Elab.Command
meta import Lean

/-!
# Audit of the standalone Gaussian SYK statements

The public CLT statements must use only mathlib and definitions from `SYK.Main`.
Follow types, definition bodies, and constructor types, but never theorem proofs.
`import all` makes the unexposed bodies in `SYK.Main` available to this audit.
-/

namespace SYK.MainAudit

open Lean Elab Command

/-- Reject transitive statement dependencies on SYK modules other than `SYK.Main`. -/
public meta def checkStatements (roots : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut pending : Array Name := #[]
  for root in roots do
    let some info := env.find? root | throwError "Missing audit root: {root}"
    pending := pending ++ info.type.getUsedConstants
  let mut seen : Std.HashSet Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then
      continue
    seen := seen.insert name
    let some info := env.find? name | throwError "Missing dependency: {name}"
    if let some idx := env.getModuleIdxFor? name then
      let origin := env.header.moduleNames[idx]!
      if (`SYK).isPrefixOf origin && origin != `SYK.Main then
        throwError "Standalone Main statement depends on {name} from {origin}"
    pending := pending ++ info.type.getUsedConstants
    match info with
    | .thmInfo _ => pure ()
    | .inductInfo induct => pending := pending ++ induct.ctors.toArray
    | _ =>
      if let some value := info.value? (allowOpaque := true) then
        pending := pending ++ value.getUsedConstants

run_cmd checkStatements #[
  `SYK.CLT.GaussianSYK.syk_partition_and_log_partition_clt,
  `SYK.CLT.GaussianSYK.syk_partition_clt,
  `SYK.CLT.GaussianSYK.syk_log_partition_clt]

end SYK.MainAudit
