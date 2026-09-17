import Prizeformalize

open Lean in
#eval show Lean.CoreM _ from do
  let axs1 ← Lean.collectAxioms ``Rad.rademacher
  let axs2 ← Lean.collectAxioms ``Rad.rademacher_core
  return s!"rademacher: {axs1} | core: {axs2}"
