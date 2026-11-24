import YM.Integration.WilsonOriginalAlternativeHearing
import YM.Integration.WilsonPositionThermometerDepositedFaces

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeVane
open Extra.Trajectories FVA1 RG05Readout.Records
open Set Function Filter Finset MeasureTheory Lattice Wilson RG Source Extraction Table Spec Marker
open Climb Trace.Pilot Next.Rank Next.UVStress PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Accent MergeProof.East MergeProof.Replicums
open OriginalForcedAddresses Push.GridApprox.Nil WilsonPositionThermometerDepositedFaces WilsonOriginalAlternativeHearing
open scoped Topology Classical BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple) (N per:ℕ)
    {I:Type} [DecidableEq I] [Fintype I] {D:ℕ} (A:Vane R.family D) (j:I→Fin (D+1))
    (v:∀i,(Bel R.family.book).Field (j i)) (o:Positions I (R.family.side N per)) {k f:ℕ}

/-- On the received filtration each complete bare subproduct, including its
true disconnected contributions, is heard from the same fixed bare cutoff. -/
theorem original (high:k≤N) (ref:∀a,R.family.ref (j a)≤N) (s:(Replicum.Bud I).Mode) (lower:f≤k) :
    held R.family N per (fun U=>(gust R.family.path N per N (pages R simple N per A j v o) k high U).part s) lower =
      actualTransport R.family (N:=N) (fun U=>∏a∈s.val,R.family.O N per
        (A.wheel.atCut (N,per) (j a) (v a)) (o.origin a) U) (lower.trans high) := by
  let g:=fun U=>∏a∈s.val,R.family.O N per (A.wheel.atCut (N,per) (j a) (v a)) (o.origin a) U
  have cancel:(fun U:Config G (R.family.side k per)=>((R.family.path.rep N per k).eval U)⁻¹ •
      (gust R.family.path N per N (pages R simple N per A j v o) k high U).part s)=
      actualTransport R.family (N:=N) g high:=by
    funext U
    have pos:0<(R.family.path.rep N per k).eval U:=Multi.AxisShift.chosen_positive R.makes.wilson high U
    rw [deposited R simple N per A j v o ref high s U,smul_smul,
      inv_mul_cancel₀ pos.ne',one_smul]
  rw [normalized R.family N per R.makes high,cancel]
  exact actualTransport_tower R.family R.makes (Nat.le_refl N) g high lower

theorem planted {W:Rep G (R.family.side k per)} (high:k≤N)
    (quiet:W.eval=(R.family.path.rep N per k).eval) (g:Config G (R.family.side k per)→ℂ) (lower:f≤k) :
    held R.family N per (fun U=>(W.eval U:ℂ)*g U) lower=actualTransport R.family (N:=N) g lower := by
  rw [normalized R.family N per R.makes high]
  apply congrArg (fun h=>actualTransport R.family (N:=N) h lower)
  funext U
  have pos:0<(R.family.path.rep N per k).eval U:=Multi.AxisShift.chosen_positive R.makes.wilson high U
  rw [quiet,← Complex.real_smul,smul_smul,inv_mul_cancel₀ pos.ne',one_smul]

end YM.Integration.WilsonOriginalAlternativeVane
