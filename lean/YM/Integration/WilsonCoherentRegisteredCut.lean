import YM.Integration.WilsonCoherentReportingForest
import YM.Integration.WilsonReportingForestPivotExperiment

/-! The original full reporting primary in its true restored, sampled
forest. The event, threshold and fine-side parameter all come from one run. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentRegisteredCut
open Function Filter Finset Set Lattice Wilson RG Tree RG16 Precision PertExtension
open PhysicalNext.Repeat.Legato OPE.Therm MSbar.Heath
open Source WilsonPositionSeparatedProfileReportingPrimary RG05Readout Address Native Pulse MergeProof Accent Axial Work.E08
open WilsonReportingForestPivots WilsonPhysicalRegisteredForestAction
open WilsonPhysicalLocalPlaquetteForest WilsonPositionSeparatedProfileReportingCut
open WilsonCoherentReportingForest
open scoped Classical Topology

variable {G : Gauge} (R : Run G) {I : Type} [Fintype I] (d : I→ℕ)

theorem purchased (simple : G.Simple) (p : ℕ) : ∃ C : ℝ, 0≤C ∧ ∀ᶠ m : ℕ in atTop,
    ∀N,m<N → ∀per (o : I→Site (R.family.side (m+1) per))
    (T : Forest (R.family.path.levels.clock.op m per).ratio),
    let B := incident R T d o
    let E := moving T B
    let θ := (R.family.path.rep N per (m+1)).p.threshold
    ∀(v : ({i:T.Free|i∉E}:Set T.Free) → G.El) (X : ↥E → G.Color),
    let U := restored T B v (Chart.expLinks G (↥E) X)
    ‖X‖<1 → U∈cold R m per d o → ∀(y : ∀i,R.family.label (d i)),
    ‖(∏i,Push.Local.primary (R.family.localSection (d i)) (o i) θ (y i) U) -
       WilsonCoherentReportingPivot.row R d θ y o (restored T B v 1) (drift T B X) p 1‖
       ≤ WilsonCoherentReportingPivot.mass R d θ y * (C*‖X‖^(p+1)) := by
  obtain ⟨C,pos,pay⟩ := WilsonCoherentReportingPivot.purchased R d p
  refine ⟨C,pos,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (OPE.Therm.narrow (H:=R.family.path) simple)]
    with m late N live per o T
  dsimp only
  intro v X small atCut y
  let A := R.family.path.levels
  let B := incident R T d o
  let E := moving T B
  let U := restored T B v (Chart.expLinks G (↥E) X)
  let θ := (R.family.path.rep N per (m+1)).p.threshold
  have ceiling : cool A (m+1)≤θ := by
    have same : (R.family.path.rep N per (m+1)).p=A.budget (m+1) :=
      (R.makes.wilson.represents N per (m+1) live).vac
    change 0<cool A (m+1) ∧ 4*cool A (m+1)≤A.clock.threshold (m+1) at late
    dsimp [θ];rw [same];change cool A (m+1)≤A.clock.threshold (m+1)
    linarith only [late.1,late.2]
  have good (i:I) : Healthy θ ((R.family.localSection (d i)).footprint (o i)) U :=
    healthy _ (WilsonReportingForestPivots.covers R (d i) (o i)) ceiling (Set.mem_iInter.mp atCut i)
  apply (pay _ θ y o U (restored T B v 1) (drift T B X) 1 ‖X‖ zero_lt_one (norm_nonneg _) (by simpa only [one_mul] using small) _ _ good).trans
  · simp only [one_mul]
    exact le_rfl
  · intro a
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg X)).2 fun j=>size T B X _
  · intro a j
    simpa only [one_smul] using edge T B v X 1 (RGComparison.Core16.Spool.legs _ o j)

end YM.Integration.WilsonCoherentRegisteredCut
