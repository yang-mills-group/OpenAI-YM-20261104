import YM.Integration.WilsonPositionPhysicalCellTest

/-! Graded compact Wilson words at arbitrary real radii. The fixed original
representatives admit the original ordered limits, and their moving original
ultraviolet lifts use the same elected physical draw and joint subcells. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDiagnosticCells
open Function Set Filter Metric MeasureTheory Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Lattice Wilson RG PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame Maxwell XSpace XSpace.Normalize
open Finset Source FVA2 FVA2.Register RG12 Cells Push.GridApprox XSpace.Structure1
open WilsonPositionPhysicalCellTest
open scoped Topology Classical BigOperators ContDiff
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book} {n:ℕ}
variable (F:Final R.family f S) (d:Caps n) (φ:Test n)
variable (w:UVIndex→R.family.book.Vector d) (c:R.family.book.Vector d)

def cut (r:ℝ) (z:UVIndex) (x:Points n) : ℂ :=
  R.family.ensemble (N:=z.1) (p:=z.2) d (site r z x) (w z)

include F in
theorem ordered {r:ℝ} (hr:0<r) :
    f.limits (fun p=>suitable R.family.S p (dilate hr φ))
      (fun N p=>(R.family.S.a N:ℂ)^(4*n)*∑ u:Sites R (N,p) n,
        dilate hr φ (Extraction.Order.cells R.family N p u) * R.family.ensemble (N:=N) (p:=p) d u c)
      (φ.applyTo (fun x=>S.value d (r • x) c)) := by
  have h:S.integralOn d c (dilate hr φ)=φ.applyTo (fun x=>S.value d (r • x) c) := by
    unfold Table.integralOn
    exact zoom_integral φ hr _
  rw [←h]
  exact Extraction.Order.full_read f R.family S F.room.ordered n d c (dilate hr φ)

section
variable (r : ℝ) (z : UVIndex)
private theorem visible (u : Sites R z n) : MeasurableSet (cell r z u) := by
  have grid : Measurable (address (R.family.S.a z.1) : Points n → Fin n → Cover) := by
    apply measurable_to_countable
    intro x
    exact measurable_segment (R.family.S.a_pos z.1) (address (R.family.S.a z.1) x)
  let U : Set (Fin n → Cover) := {c | wrap _ ∘ c=u}
  exact (Set.to_countable U).measurableSet.preimage (grid.comp (continuous_const_smul r).measurable)

private theorem integrate {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : Sites R z n → Points n → E) (finite : ∀ u, Integrable (h u)) :
    (∫ x, h (site r z x) x) = ∑ u, ∫ x in cell r z u, h u x := by
  have partition (x : Points n) : h (site r z x) x = ∑ u, (cell r z u).indicator (h u) x := by
    simp [Set.indicator_apply,cell]
  have paid (u : Sites R z n) := (finite u).indicator (visible r z u)
  simp_rw [partition]
  rw [integral_finsetSum _ (fun u _=>paid u)]
  exact Finset.sum_congr rfl fun u _=>integral_indicator (visible r z u) ..

end

theorem subcells (r : ℝ) (z : UVIndex) :
    φ.applyTo (cut d w r z) =
      ∑ u : Sites R z n, mass φ r z u * R.family.ensemble (N:=z.1) (p:=z.2) d u (w z) := by
  let g (u : Sites R z n) := R.family.ensemble (N:=z.1) (p:=z.2) d u (w z)
  change (∫ x, φ x*g (site r z x)) = _
  rw [integrate r z (fun u x=>φ x*g u)
    (fun u=>(φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).mul_const (g u))]
  exact Finset.sum_congr rfl (fun u _=>integral_mul_const _ _)

private theorem measurable_cut (r : ℝ) (z : UVIndex) :
    Measurable (cut d w r z) := by
  let I (x : Fin n → Cover) := R.family.ensemble (N:=z.1) (p:=z.2) d (wrap _ ∘ x) (w z)
  have grid : Measurable (address (R.family.S.a z.1) : Points n → Fin n → Cover) := by
    apply measurable_to_countable
    intro x
    exact measurable_segment (R.family.S.a_pos z.1) (address (R.family.S.a z.1) x)
  exact (measurable_of_countable I).comp (grid.comp (continuous_const_smul r).measurable)


variable {l:Filter UVIndex} (hG:G.Simple) (hl:l≤f.fuse) {r:ℝ} (hr:0<r)
variable (paid:∀ i, Tendsto (fun z=>w z i) l (𝓝 (c i)))
include F hG hl hr paid in
theorem compact {K : Set (Points n)} (hk : IsCompact K) (sep : K ⊆ conf n) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ z in l, ∀ x∈K, ‖cut d w r z x-S.value d (r•x) c‖ < ε := by
  let T := (fun x : Points n=>r • x) '' K
  have tc : IsCompact T := hk.image (continuous_const_smul r)
  have legal : T ⊆ conf n := by rintro _ ⟨x,hx,rfl⟩;exact Work.A05.smul_conf hr (sep hx)
  obtain ⟨t,ht,inside⟩ := tc.exists_cthickening_subset_open (conf_open _) legal
  let U := cthickening t T
  have uc : IsCompact U := tc.cthickening
  let result (X : Points n) := S.value d X c
  have smooth : ContinuousOn result U := ((F.room.kernel.smooth.on_conf d c).continuousOn).mono inside
  obtain ⟨δ,hδ,move⟩ := Metric.uniformContinuousOn_iff.mp (uc.uniformContinuousOn_of_continuous smooth) (ε/2) (half_pos he)
  have positive : Tendsto (fun z : UVIndex=>z.1) l atTop :=
    tendsto_atTop.mpr fun j=>(large_mesh f j).filter_mono hl
  have fine : Tendsto (fun z : UVIndex=>(4*n:ℝ)*R.family.S.a z.1) l (𝓝 0) := by
    simpa using (tendsto_const_nhds (x:=(4*n:ℝ))).mul (R.family.S.shrinks.comp positive)
  have bank := WilsonMovingCalibratedFields.paid R hG F hl d w c paid U uc inside (ε/2) (half_pos he)
  filter_upwards [bank,fine.eventually (gt_mem_nhds (lt_min ht hδ))] with z valid mesh x hx
  let X := r • x
  let a := address (R.family.S.a z.1) X
  let Y := tag (R.family.S.a z.1) a
  have tx : X ∈ T := ⟨x,hx,rfl⟩
  have near : dist Y X < min t δ := (Extraction.approximate (R.family.S.a_pos z.1) X).trans_lt mesh
  have uy : Y ∈ U := mem_cthickening_of_dist_le Y X t T tx (near.le.trans (min_le_left _ _))
  change ‖R.family.ensemble d (wrap _ ∘ a) (w z) - result X‖ < ε
  rw [←dist_eq_norm]
  exact (dist_triangle _ (result Y) _).trans_lt ((add_lt_add (valid a uy)
    (move Y uy X (self_subset_cthickening T tx) (near.trans_le (min_le_right _ _)))).trans_eq (add_halves ε))

include F hG hl hr paid in
theorem signed : Tendsto (fun z=>φ.applyTo (cut d w r z)) l (𝓝 (φ.applyTo (fun x=>S.value d (r•x) c))) := by
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
  have target := φ.smearing (((F.room.kernel.smooth.on_conf d c).continuousOn).comp
    (continuous_const_smul r).continuousOn (fun _ hx=>Work.A05.smul_conf hr hx))
  have input := φ.smearing (continuousOn_const (c:=(1:ℂ)) (s:=conf n))
  have gi : Integrable (fun x : Points n=>φ x) := by simpa using input
  filter_upwards [compact F d w c hG hl hr paid φ.hasCompactSupport φ.tsupport_subset ht] with z points
  let W := cut d w r z
  have actual : AEStronglyMeasurable (fun x : Points n=>φ x*W x) volume :=
    (φ.continuous.measurable.mul (measurable_cut d w r z)).aestronglyMeasurable
  have point (x : Points n) : ‖φ x*W x-φ x*S.value d (r•x) c‖ ≤ ‖φ x‖*t := by
    by_cases empty : φ x=0
    · simp [empty]
    rw [←mul_sub,norm_mul]
    exact mul_le_mul_of_nonneg_left (points x (subset_closure empty)).le (norm_nonneg _)
  have original : Integrable (fun x : Points n=>φ x*S.value d (r•x) c) := target
  have di := (gi.norm.mul_const t).mono' (actual.sub original.aestronglyMeasurable) (Eventually.of_forall point)
  have vi : Integrable (fun x : Points n=>φ x*W x) :=
    (di.add original).congr (Eventually.of_forall fun _=>sub_add_cancel _ _)
  rw [dist_eq_norm]
  change ‖(∫ x,φ x*W x)-(∫ x,φ x*S.value d (r•x) c)‖ < ε
  rw [←integral_sub vi original]
  exact (norm_integral_le_of_norm_le (gi.norm.mul_const t) (Eventually.of_forall point)).trans_lt
    ((integral_mul_const ..).trans_lt budget)

end YM.Integration.WilsonPositionOriginalDiagnosticCells
