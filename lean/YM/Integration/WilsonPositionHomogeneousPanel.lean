import YM.Integration.WilsonPositionMeasuredRawPanel
import YM.Integration.WilsonMovingCalibratedFields

/-! The compact left side of the independent raw-panel comparison on the
original Wilson measure. Moving cutoff labels may use their own original
calibrated lifts; every occupied slot lies in the same configuration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionHomogeneousPanel
open Filter Function Finset Set Metric MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open OPE OPE.Orbits Climb Trace.Pilot Next.UVStress RG12 RG17 PhysMS PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Structure1 Maxwell FVA2 FVA2.Register Cells Push.GridApprox
open WilsonPositionSeparatedProfileMatching
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → PhysMS.tower S) (Z : WilsonPrescription G)
    (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n)

def field (r : ℝ) (i : Fin n) : S.Field d :=
  WilsonPositionHomogeneousFrame.homogeneous F J Z r d ((Maxwell.Free.fields R.family.labels d).symm (v i))

def profile (r : ℝ) : Points n → ℂ := measured F none (WilsonPositionHomogeneousFrame.homogeneous F J Z r)
    (d:=fun _ : Fin n=>d) (fun i => (Maxwell.Free.fields R.family.labels d).symm (v i)) r

def reading (r : ℝ) (w : UVIndex → Fin n → R.family.label d) (z : UVIndex) (x : Points n) : ℂ :=
  R.family.ensemble (N:=z.1) (p:=z.2) (fun _ : Fin n=>d)
    (wrap _ ∘ address (R.family.S.a z.1) (r • x)) (w z)

def panel (r : ℝ) (w : UVIndex → Fin n → R.family.label d) (z : UVIndex) : ℂ :=
  φ.applyTo (reading d r w z)

theorem formula (r : ℝ) (w : UVIndex → Fin n → R.family.label d) (z : UVIndex) (x : Points n) :
    reading d r w z x = R.family.omega z.1 z.2 (fun U => ∏ i : Fin n, R.family.O z.1 z.2
      (w z i) (wrap _ (address (R.family.S.a z.1) (r • x) i)) U) := rfl

private theorem cells (r : ℝ) (w : UVIndex → Fin n → R.family.label d) (z : UVIndex) :
    Measurable (reading d r w z) := by
  let I (x : Fin n → Cover) := R.family.ensemble (N:=z.1) (p:=z.2) (fun _ : Fin n=>d) (wrap _ ∘ x) (w z)
  have grid : Measurable (address (R.family.S.a z.1) : Points n → Fin n → Cover) := by
    apply measurable_to_countable
    intro x
    exact measurable_segment (R.family.S.a_pos z.1) (address (R.family.S.a z.1) x)
  exact (measurable_of_countable I).comp (grid.comp (continuous_const_smul r).measurable)

variable (hG : G.Simple) {l : Filter UVIndex} (hl : l ≤ f.fuse)
    {r : ℝ} (hr : 0 < r) (w : UVIndex → Fin n → R.family.label d) (c : Fin n → R.family.label d)
    (paid : ∀ i, Tendsto (fun z=>w z i) l (𝓝 (c i))) (filed : ∀ i, S.project d (c i) = field F J Z d v r i)
local notation "raw" => profile F J Z d v r

include hG hl hr paid filed in
theorem compact {K : Set (Points n)} (hk : IsCompact K) (sep : K ⊆ conf n) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ z in l, ∀ x∈K, ‖reading d r w z x-raw x‖ < ε := by
  let T := (fun x : Points n=>r • x) '' K
  have tc : IsCompact T := hk.image (continuous_const_smul r)
  have legal : T ⊆ conf n := by rintro _ ⟨x,hx,rfl⟩;exact Work.A05.smul_conf hr (sep hx)
  obtain ⟨t,ht,inside⟩ := tc.exists_cthickening_subset_open (conf_open _) legal
  let U := cthickening t T
  have uc : IsCompact U := tc.cthickening
  let result (X : Points n) := S.value (fun _=>d) X c
  have smooth : ContinuousOn result U := ((F.room.kernel.smooth.on_conf (fun _=>d) c).continuousOn).mono inside
  obtain ⟨δ,hδ,move⟩ := Metric.uniformContinuousOn_iff.mp (uc.uniformContinuousOn_of_continuous smooth) (ε/2) (half_pos he)
  have positive : Tendsto (fun z : UVIndex=>z.1) l atTop :=
    tendsto_atTop.mpr fun j=>(large_mesh f j).filter_mono hl
  have fine : Tendsto (fun z : UVIndex=>(4*n:ℝ)*R.family.S.a z.1) l (𝓝 0) := by
    simpa using (tendsto_const_nhds (x:=(4*n:ℝ))).mul (R.family.S.shrinks.comp positive)
  have bank := WilsonMovingCalibratedFields.paid R hG F hl (fun _ : Fin n=>d) w c paid U uc inside (ε/2) (half_pos he)
  filter_upwards [bank,fine.eventually (gt_mem_nhds (lt_min ht hδ))] with z valid mesh x hx
  let X := r • x
  let a := address (R.family.S.a z.1) X
  let Y := tag (R.family.S.a z.1) a
  have tx : X ∈ T := ⟨x,hx,rfl⟩
  have near : dist Y X < min t δ := (Extraction.approximate (R.family.S.a_pos z.1) X).trans_lt mesh
  have uy : Y ∈ U := mem_cthickening_of_dist_le Y X t T tx (near.le.trans (min_le_left _ _))
  have fit : raw x = result X := by
    change S.classMoment S (fun _ => d) X (field F J Z d v r) = _
    rw [show field F J Z d v r = fun i=>S.project d (c i) from funext (fun i=>(filed i).symm)]
    exact S.at_project S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) (legal tx) (fun i=>⟨d,c i⟩)
  rw [fit,←dist_eq_norm]
  exact (dist_triangle _ (result Y) _).trans_lt ((add_lt_add (valid a uy)
    (move Y uy X (self_subset_cthickening T tx) (near.trans_le (min_le_right _ _)))).trans_eq (add_halves ε))

include hG hl hr paid filed in
theorem signed : Tendsto (panel d φ r w) l (𝓝 (observed Z F J none d φ v r)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε he
  let M := WilsonPositionPhaseProfileTest.mass φ
  have hm : 0 ≤ M := integral_nonneg fun _=>norm_nonneg _
  let t := (ε/2)/(M+1)
  have ht : 0 < t := div_pos (half_pos he) (by linarith)
  have budget : M*t < ε := calc
    M*t ≤ (M+1)*t := mul_le_mul_of_nonneg_right (by linarith) ht.le
    _ = ε/2 := by dsimp [t];field_simp
    _ < ε := half_lt_self he
  have target := φ.smearing (WilsonPositionPhaseProfileTest.smooth F J Z (d:=fun _ : Fin n=>d) none
    (fun i=>(Maxwell.Free.fields R.family.labels d).symm (v i)) hr)
  have input := φ.smearing (continuousOn_const (c:=(1:ℂ)) (s:=conf n))
  have gi : Integrable (fun x : Points n=>φ x) := by simpa using input
  filter_upwards [compact F J Z d v hG hl hr w c paid filed φ.hasCompactSupport φ.tsupport_subset ht] with z points
  let W := reading d r w z
  have actual : AEStronglyMeasurable (fun x : Points n=>φ x*W x) volume :=
    (φ.continuous.measurable.mul (cells d r w z)).aestronglyMeasurable
  have point (x : Points n) : ‖φ x*W x-φ x*raw x‖ ≤ ‖φ x‖*t := by
    by_cases empty : φ x=0
    · simp [empty]
    rw [←mul_sub,norm_mul]
    exact mul_le_mul_of_nonneg_left (points x (subset_closure empty)).le (norm_nonneg _)
  have original : Integrable (fun x : Points n=>φ x*raw x) := target
  have di := (gi.norm.mul_const t).mono' (actual.sub original.aestronglyMeasurable) (Eventually.of_forall point)
  have vi : Integrable (fun x : Points n=>φ x*W x) :=
    (di.add original).congr (Eventually.of_forall fun _=>sub_add_cancel _ _)
  rw [dist_eq_norm]
  change ‖(∫ x,φ x*W x)-(∫ x,φ x*raw x)‖ < ε
  rw [←integral_sub vi original]
  exact (norm_integral_le_of_norm_le (gi.norm.mul_const t) (Eventually.of_forall point)).trans_lt
    ((integral_mul_const ..).trans_lt budget)

include hG hl hr in
theorem representatives :
    Tendsto (panel (R:=R) d φ r (fun _ i=>S.representative d (field F J Z d v r i))) l
      (𝓝 (observed Z F J none d φ v r)) :=
  signed F J Z d φ v hG hl hr _ _ (fun _=>tendsto_const_nhds) (fun _=>S.rep _ _)

end YM.Integration.WilsonPositionHomogeneousPanel
