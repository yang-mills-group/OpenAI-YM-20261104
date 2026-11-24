import YM.Integration.WilsonThermometerUnitFilingCylinder
import YM.Integration.WilsonThermometerUnitFilingWindow

/-! The actual compact signed thermometer equals its captured value plus
its finite signed unit feeds, up to the measured replica and stable prices. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingMeasured
open Function Set Filter MeasureTheory Lattice Wilson RG Source Labels OPE Bid Cells Real Marker
open MergeProof Ribbons Accent ManyCopies RG16 RG16.Literal Trace.Physical.GermGraph
open PhysicalNext.Repeat.Legato Pert.Asymptotics XSpace WilsonPositionThermometerCapStation
open WilsonThermometerUnitFilingFeed WilsonThermometerUnitFilingCylinder
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) (simple : G.Simple)
local notation "j!" => Stock.census (Fin 3)

include simple in
private theorem replica {N p j : ℕ} (live : R.family.ref 0 ≤ N) (jN : j ≤ N)
    (Y : Cut R.family N p) (hf : Continuous Y) (B : R.family.label 0) (e : ℝ)
    (inside : Interior ((center R.family.S p jN 0).chamber 0) (Y-R.family.O N p B 0))
    (price : (center R.family.S p jN 0).rootTest (R.family.beta N p) (Y-R.family.O N p B 0) ≤ e) :
    ‖R.family.omega N p Y-B 0‖ ≤ e := by
  let F := R.family.labels.level 0
  have unit : R.family.O N p B 0=B 0 • (1:Cut R.family N p) := by
    obtain ⟨z,ez⟩ := RG12.unit_spans simple R.family 0 (R.family.ref 0) (by decide) B
    rw [ez,(R.family.linearO N p 0 0).map_smul]
    have ready := R.family.constant R.makes 0 (p:=p) live 0
    change R.family.O N p (unitVec F R.family.path (R.family.ref 0)) 0=1 at ready
    rw [ready]
    simp [unitVec,Labels.Frame.e0]
  have bill := (OPE.Strobe.atone (Q:=Y-R.family.O N p B 0) (center R.family.S p jN 0)
    (R.family.beta N p) (seamless R.makes N p) inside).trans price
  have hearing : R.family.omega N p (Y-R.family.O N p B 0)=R.family.omega N p Y-B 0 := by
    rw [unit]
    unfold Family.omega moment
    simp only [Pi.one_def,Pi.sub_apply]
    rw [integral_sub]
    · simp [probReal_univ]
    · exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · exact integrable_const _
  change ‖R.family.omega N p (Y-R.family.O N p B 0)‖ ≤ e at bill
  rwa [hearing] at bill

include simple in
private theorem offset {N p u i b : ℕ} (ui : u ≤ i) (ib : i ≤ b) (bN : b<N)
    (aopen : ∀ k, u ≤ k → k ≤ b → Opened R.family 0 k p)
    (Y : Cut R.family N p) (B : R.family.label 0) {a : ℝ}
    (ret : WholeProductCapture.Retained R.family N b p 0 u R.makes (aopen u le_rfl (ui.trans ib))
      (ui.trans ib) bN Y B a) :
    gainChart R.family.path b i * ‖report R Y i-B 0‖ ≤ a := by
  let oi := aopen i ui ib
  have edge := ib.trans bN.le
  have price := WilsonCapturedRetainedProjection.measured R 0 (aopen u le_rfl (ui.trans ib)) (ui.trans ib) bN ui ib oi Y B a ret
  rw [scalar_cost R simple oi edge,Pi.sub_apply] at price
  have back : (R.family.factory 0 N p).terminal.symm B=B :=
    (terminal R simple (oi.post.trans edge) _).symm.trans ((R.family.factory 0 N p).terminal.apply_symm_apply B)
  simp only [report,dif_pos (And.intro oi edge),terminal R simple (oi.post.trans edge)]
  simpa only [back] using price

private theorem price {b i : ℕ} {g : ℝ} (gp : 0<g) (P K : ℕ)
    (span : 8*((P:ℝ)+K)*log g⁻¹ ≤ R.family.S.scale b-R.family.S.scale i) :
    (g⁻¹)^K ≤ gainChart R.family.path b i*g^P := by
  calc
    _ = exp ((K:ℝ)*log (g⁻¹)) := by rw [Real.exp_nat_mul,Real.exp_log (inv_pos.mpr gp)]
    _ ≤ exp ((1/8:ℝ)*(R.family.S.scale b-R.family.S.scale i)+(P:ℝ)*log g) := by
      apply exp_le_exp.mpr
      rw [Real.log_inv] at span ⊢
      linarith
    _ = _ := by rw [Real.exp_add,Real.exp_nat_mul,Real.exp_log gp]; rfl

include simple in
/-- The chosen cutoff of the feed is common to all N,p. The physical receipt
is one actual retained trajectory together with the reflected Wilson test
of its difference from that very scalar ticket. -/
theorem original (slow : WilsonWindowReportingPace.Slow R.kit) (A : Group R.family 6) (u K P : ℕ) :
    ∀ᶠ b : ℕ in atTop, ∃ i : ℕ, ∃ ui : u ≤ i, ∃ ib : i ≤ b, ∀ N p : ℕ, ∀ bN : b<N,
      let z : RG12.UVIndex := (N,p)
      let g:=regulatorRun R.family N p b
      R.family.S.scale b-R.family.S.scale i ≤ 4*(8*((P:ℝ)+K)+1)*log g⁻¹ ∧
      ∀ (r : ℝ) (φ : Test 3) (Q : Sites R z→Poly j!)
        (aopen : ∀ k, u ≤ k → k ≤ b → Opened R.family 0 k p) (B : R.family.label 0) (a e : ℝ),
        let Y:=WilsonThermometerUnitFilingCylinder.cylinder R A z r φ Q
        WholeProductCapture.Retained R.family N b p 0 u R.makes (aopen u le_rfl (ui.trans ib)) (ui.trans ib) bN Y B a →
        a ≤ (g⁻¹)^K → ∀ (j : ℕ) (jN : j ≤ N),
        Interior ((center R.family.S p jN 0).chamber 0) (Y-R.family.O N p B 0) →
        (center R.family.S p jN 0).rootTest (R.family.beta N p) (Y-R.family.O N p B 0) ≤ e →
        ‖WilsonThermometerUnitFilingCylinder.tested R A z r φ Q-
          (report R Y b+∑k ∈ Finset.Ico i b,(report R Y k-report R Y (k+1)))‖ ≤ e+g^P := by
  filter_upwards [WilsonThermometerUnitFilingWindow.original R simple slow u (8*(P+K))] with b issued
  obtain ⟨i,ui,ib,all⟩ := issued
  refine ⟨i,ui,ib,?_⟩
  intro N p bN z g
  obtain ⟨gp,_,scope,roof⟩ := all N p bN.le
  push_cast at scope roof
  refine ⟨roof,?_⟩
  intro r φ Q aopen B a e Y ret bought j jN inside space
  have live := (aopen u le_rfl (ui.trans ib)).post.trans ((ui.trans ib).trans bN.le)
  have packed := replica R simple live jN Y (continuous_cylinder R A z r φ Q) B e inside space
  have ticket := offset R simple ui ib bN aopen Y B ret
  have rent := (ticket.trans bought).trans (price R gp P K scope)
  have tiny : ‖report R Y i-B 0‖ ≤ g^P := le_of_mul_le_mul_left rent (Real.exp_pos _)
  let f := report R Y
  have sum : (∑k ∈ Finset.Ico i b,(f k-f (k+1)))=f i-f b := by
    rw [Finset.sum_Ico_eq_sub _ ib]
    simp_rw [show (fun k : ℕ=>f k-f (k+1))=(fun k=> -(f (k+1)-f k)) by funext k;abel,
      Finset.sum_neg_distrib,Finset.sum_range_sub]
    abel
  change ‖WilsonThermometerUnitFilingCylinder.tested R A z r φ Q-(f b+∑k ∈ Finset.Ico i b,(f k-f (k+1)))‖ ≤ _
  rw [←WilsonThermometerUnitFilingCylinder.literal R A z r φ Q,sum,show f b+(f i-f b)=f i by abel]
  exact (show ‖R.family.omega N p Y-f i‖ ≤ ‖R.family.omega N p Y-B 0‖+‖f i-B 0‖ by
    simpa only [dist_eq_norm,norm_sub_rev (B 0) (f i)] using dist_triangle (R.family.omega N p Y) (B 0) (f i)).trans
    (add_le_add packed tiny)

end YM.Integration.WilsonThermometerUnitFilingMeasured
