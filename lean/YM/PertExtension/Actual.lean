import YM.PertExtension.UVBranch
import YM.PertExtension.Running

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace YM.PertExtension
open Extraction
variable {G : Gauge}

/-- Partial physical endpoint: compatible with sampled unselected Maxwell and
stress UV results in `Actual`, including one extraction of the scalar ledger,
on a Family given by the construction proving CLOSED. -/
theorem actual_exists (h : G.Simple) : ∃ (C : Family G) (f : Order) (S : Table C.book) (B : ℕ→ℝ), Running.isLimit C f B ∧ Nonempty (Actual C f S) := by
  obtain ⟨C,hM,-,-,-,g,S,⟨A⟩⟩:=temple h 1 zero_lt_one Order.full
  let f := Order.full.refine g
  change Actual C f S at A
  obtain ⟨p,B,hB⟩ := Running.extraction C hM f
  exact ⟨C,f.refine p,S,B,fun m=>Order.along (hB m), ⟨⟨A.F.onward p, A.E, A.same, A.incl, A.diff,A.M,A.I,Next.UVStress.onward_uv A.M A.I A.uv p,A.nonzero,A.zero_v,A.curve,A.approaches,A.aligned,A.calibrated,A.free_stress,A.free_rank,A.stress⟩⟩⟩
end YM.PertExtension
