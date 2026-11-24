import YM.Integration.WilsonPositionThermometerStationBirth

/-! All physical legs on the same cutoff and at their own field horizons.
The complete old vacuum and every real hard row are present in the birth. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerGradedBirth
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Source Extraction Table Spec Marker FVA1
open Climb Trace.Pilot Next.UVStress Next.Rank RG12 RG17 PhysMS PhysicalNext.Repeat.Legato
open MergeProof MergeProof.East MergeProof.Accent MergeProof.Replicums
open Push.GridApprox.Nil OriginalForcedAddresses ActualRunUnmaskedPartners
open scoped Topology Classical BigOperators
variable {G : Gauge} (R : Run G) (N p : ℕ) {I : Type} [DecidableEq I] [Fintype I]
    {D : ℕ} (V : Vane R.family D) (j : I → Fin (D+1)) (v : ∀ i, (Bel R.family.book).Field (j i))

def payload (i : I) : R.family.label (j i) := Price.awake R.family (j i) N N p (V.wheel.atCut (N,p) (j i) (v i))

private theorem log_read (ref : ∀ i, R.family.ref (j i) ≤ N)
    (o : Positions I (R.family.side N p)) (U : Config G (R.family.side N p)) :
    actualLog R N p N o (fun i => (j i).val) (payload R N p V j v) U =
    Mach (Replicum.Bud I) (fun i => R.family.O N p (V.wheel.atCut (N,p) (j i) (v i)) (o.origin i) U) := by
  unfold actualLog
  simp only [payload,WilsonPositionThermometerStationBirth.kernel R N p _ (ref _) ]

theorem original (simple : G.Simple) (ref : ∀ i, R.family.ref (j i) ≤ N)
    (o : Positions I (R.family.side N p)) (U : Config G (R.family.side N p)) :
    essence (ActualRunFullPages.pages R simple N p N le_rfl o (fun i => (j i).val)
      (payload R N p V j v)) (fun _=>0) (fun _=>1) U =
    ((R.family.path.rep N p N).eval U : ℂ) • Poly.pass (Mach (Replicum.Bud I) (fun i =>
      R.family.O N p (V.wheel.atCut (N,p) (j i) (v i)) (o.origin i) U)) := by
  calc
    _ = fullInput R N p N o (fun i => (j i).val) (payload R N p V j v) U :=
      ActualRunFullPages.essence_full R simple N p N le_rfl o (fun i => (j i).val)
        (payload R N p V j v) ref U
    _ = _ := congrArg (fun a : Poly (Replicum.Bud I) => ((R.family.path.rep N p N).eval U : ℂ) • Poly.pass a)
      (log_read R N p V j v ref o U)

end YM.Integration.WilsonPositionThermometerGradedBirth
end
