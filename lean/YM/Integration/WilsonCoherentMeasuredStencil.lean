import YM.Integration.WilsonCoherentForestReadout
import YM.Integration.WilsonIncidentPhysicalTaylor

/-! The physical cutoff selects the genuine unmasked canonical reporting
section in the original compact integral. The retained Taylor order absorbs
the threshold at all the inputs before the period is specified. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentMeasuredStencil
open Function Filter Set Metric Lattice Wilson RG Tree RG16 Precision PertExtension
open PhysicalNext.Repeat.Legato OPE.Therm MSbar.Heath Source Pert.Asymptotics
open WilsonReportingForestPivots WilsonCoherentForestMeasure WilsonCoherentForestReadout WilsonIncidentRegisteredMass
open WilsonPhysicalRegisteredLocalAction WilsonReportingRegisteredForest WilsonPositionSeparatedProfileReportingCut
open scoped Classical Topology
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I] (d:I→ℕ)

def mark {n:Side} (o:I→Site n) (θ:ℝ) (y:∀i,R.family.label (d i)) (c:ℂ) (χ:ℂ→L[ℝ]ℝ) (U:Config G n):ℝ :=
  χ (c*∏i,Push.Local.presented (R.family.localSection (d i)) (o i) θ (y i) U)

theorem legitimate {n:Side} (o:I→Site n) (θ:ℝ) (y:∀i,R.family.label (d i)) (c:ℂ) (χ:ℂ→L[ℝ]ℝ) :
    Envelope (mark R d o θ y c χ) ∧ GaugeInvariant (mark R d o θ y c χ) := by
  have cont:Continuous (mark R d o θ y c χ):=
    χ.continuous.comp (continuous_const.mul (continuous_finsetProd _ (fun i _=>(R.family.localSection (d i)).continuous_places _ _)))
  refine ⟨⟨cont.measurable,(isCompact_univ.exists_bound_of_continuousOn cont.continuousOn).imp fun _ a U=>a U (mem_univ U)⟩,?_⟩
  intro g U
  have each (i:I) : Push.Local.presented (R.family.localSection (d i)) (o i) θ (y i) (Lattice.gauge g U)=
      Push.Local.presented (R.family.localSection (d i)) (o i) θ (y i) U :=
    (R.family.localSection (d i)).placed_invariant (R.makes.sections (d i)) (o i) _ g U
  simp only [mark,each]

theorem on_event (simple:G.Simple) : ∀ᶠ m:ℕ in atTop,∀ N per, m+1≤N→
    ∀ (o:I→Site (R.family.side (m+1) per)) (y:∀i,R.family.label (d i)) (U),U∈cold R m per d o→
    let θ:=(R.family.path.rep N per (m+1)).p.threshold
    (∏i,Push.Local.presented (R.family.localSection (d i)) (o i) θ (y i) U)=
    ∏i,Push.Local.primary (R.family.localSection (d i)) (o i) θ (y i) U := by
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (OPE.Therm.narrow (H:=R.family.path) simple)] with m late N per live o y U cold
  let A:=R.family.path.levels
  let θ:=(R.family.path.rep N per (m+1)).p.threshold
  have cap:cool A (m+1)≤θ:=by
    have same:(R.family.path.rep N per (m+1)).p=A.budget (m+1):=(R.makes.wilson.represents N per (m+1) live).vac
    change 0<cool A (m+1) ∧ 4*cool A (m+1)≤A.clock.threshold (m+1) at late
    dsimp [θ];rw [same];change cool A (m+1)≤A.clock.threshold (m+1)
    linarith only [late.1,late.2]
  apply Finset.prod_congr rfl
  intro i _
  exact (Push.Local.presented_primary _ (R.makes.sections (d i)) (y i) U
    (WilsonPositionSeparatedProfileReportingPrimary.healthy _ (WilsonReportingForestPivots.covers R (d i) (o i)) cap (Set.mem_iInter.mp cold i))).symm

theorem purchased (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (J:Voice G) (clear:Clear G J) (P:ChartRatio G) {r:ℝ} (pr:0<r) (sr:r<Chart.small G P)
    (q:ℕ) {ε:ℝ} (he:0<ε) :
    ∀ᶠ m:ℕ in atTop,∀N per, m+1≤N→∀(y:∀i,R.family.label (d i)) (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (c:ℂ) (χ:ℂ→L[ℝ]ℝ),
    let B:=incident R T d o
    let θ:=(R.family.path.rep N per (m+1)).p.threshold
    ∀ z:Sample T B G,z.2∈ball 0 r → state T B z∈cold R m per d o→
    ‖mark R d o θ y c χ (state T B z) - χ (c * polynomial T B R d θ y o (q+2*reserve R d) z)‖ ≤
      (‖χ‖*‖c‖)*(ε*regulatorRun R.family N per (m+1)^q*originalMass R d y) := by
  filter_upwards [on_event R d simple,WilsonIncidentPhysicalTaylor.purchased R simple slow J clear P pr sr d q he]
    with m healthy priced N per live y o T c χ
  intro B θ z hz hc
  have old:=healthy N per live o y (state T B z) hc
  have pay:=priced N per live y o T z.1 z.2 hz hc
  unfold mark
  rw [old,←map_sub,←mul_sub]
  change ‖χ (c*_)‖≤_
  calc
    _ ≤ ‖χ‖*‖c*_‖ := χ.le_opNorm _
    _ = (‖χ‖*‖c‖)*_ := by rw [norm_mul,mul_assoc];rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left pay (mul_nonneg (norm_nonneg _) (norm_nonneg _))

end YM.Integration.WilsonCoherentMeasuredStencil
