import YM.RG11Scheme.Mesh.Walk
import YM.Pert.Rig.Tiles
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! Vertex integration on the cover. Rectangular cells with upper-corner root. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11Scheme.Mesh
open Lattice Function Filter Set MeasureTheory Pert Pert.Full Metric
open scoped Topology BigOperators Classical
variable {n : Side}
variable {h:ℝ}
def pad (h:ℝ) (z:E4) : Cover := Extraction.address h (points fun _:Fin 1=> z) 0
def cell (h:ℝ) (x:Cover) := {z:E4 | pad h z=x}
lemma cartesian (hp : 0<h) (x:Cover) : cell h x=WithLp.ofLp ⁻¹' Set.pi univ (fun w=>Extraction.tile h (x w)) := by
    ext z; change (pad h z=x)↔ _; constructor
    · exact fun he a _=>(Extraction.tile_bounds hp (z a) (x a)).mp (congrFun he a)
    intro hu; exact funext (fun a=> (Extraction.tile_bounds hp (z a) (x a)).mpr (hu a (mem_univ _)))
private lemma preserves : MeasurePreserving (WithLp.ofLp (V:=Axis→ℝ) (p:=2)) volume volume := PiLp.volume_preserving_ofLp _
lemma cell_meas (hp : h>0) (x:Cover) : MeasurableSet (cell h x) := by rw [cartesian hp]; exact preserves.measurable (MeasurableSet.pi countable_univ fun _ _=>measurableSet_Ioc)
lemma cell_area (hp : h>0) (x:Cover) : volume (cell h x)= ENNReal.ofReal (h^4) := by
    rw [cartesian hp,preserves.measure_preimage]; rotate_left
    · exact (MeasurableSet.pi countable_univ fun _ _=>measurableSet_Ioc).nullMeasurableSet
    change (Measure.pi (fun _:Axis=>volume)) _=_; rw [Measure.pi_pi]
    simp_rw [show ∀ i, volume (Extraction.tile h (x i))=ENNReal.ofReal h from fun i=>by rw [Extraction.tile,Real.volume_Ioc]; ring_nf]
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin, ← ENNReal.ofReal_pow hp.le, Axis]
lemma cell_width (hp:h>0) (z:E4) : ‖h • row (pad h z)-z‖ ≤ 4*h := by
    let x:Points 1:=points fun _=>z
    have he:=PiLp.norm_apply_le (Extraction.tag h (Extraction.address h x)-x) 0
    have hL:=Extraction.approximate hp x -- not binder S!
    rw [dist_eq_norm] at hL; rw [←inc_row]
    exact he.trans (by simpa only [Nat.cast_one,mul_one] using hL)
lemma coin (hp:h>0) (z:E4) : ‖z‖ ≤ 6*h*wide (pad h z) := by
    have he:=norm_sub_le (h • row (pad h z)) (h • row (pad h z)-z)
    rw [sub_sub_cancel] at he; apply he.trans; rw [norm_smul,Real.norm_of_nonneg hp.le]; grw [cell_width hp,axis_elev]; unfold wide; nlinarith [Nat.cast_nonneg (α:=ℝ) (elev (pad h z))]
lemma plots (T : Align.Itinerary) (z : E4) : Tendsto (fun i=>incVec (T.gap i) (pad (T.gap i) z)) atTop (𝓝 z) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have ev (i) : dist (incVec (T.gap i) (pad (T.gap i) z)) z ≤ 4*T.gap i := by rw [dist_eq_norm,inc_row];apply cell_width (T.positive i)
    exact squeeze_zero (fun i=>dist_nonneg) ev (by simpa only [mul_zero] using T.cutoff.const_mul 4)
lemma full_pad (h:ℝ) : ⋃ x:Cover, cell h x=univ := eq_univ_iff_forall.mpr fun x=> mem_iUnion.mpr ⟨pad h x,rfl⟩
lemma pad_pair (h:ℝ) : Pairwise fun s t:Cover=> Disjoint (cell h s) (cell h t) := fun _ _ hn=> Set.disjoint_left.mpr fun _ (hs:_=_) (ht:_=_) => hn (hs.symm.trans ht)

variable {E:Type*} [NormedAddCommGroup E]
theorem pad_strong (hp : h>0) (m:Cover→E) : AEStronglyMeasurable (m ∘ pad h) volume := by
    have he x : AEStronglyMeasurable (m ∘ pad h) (volume.restrict (cell h x)) := aestronglyMeasurable_const.congr (f:=(fun _:E4=> m x)) (ae_restrict_of_forall_mem (cell_meas hp x) (fun y hy=> (congrArg m hy).symm))
    simpa only [full_pad, Measure.restrict_univ] using! AEStronglyMeasurable.iUnion he
variable [NormedSpace ℝ E] [CompleteSpace E]
theorem throughput (hp:h>0) {f:Cover→E} (hi : Integrable (f ∘ pad h) volume) :
   HasSum (fun x=> h^4 • f x) (∫ z,f (pad h z)) := by
    have e := hasSum_integral_iUnion (cell_meas hp) (pad_pair h) hi.integrableOn
    rw [full_pad,setIntegral_univ] at e
    have he x : ∫ z in cell h x, (f ∘ pad h) z=h^4 • f x := by
       rw [setIntegral_congr_fun (cell_meas hp x) (f:=f ∘ pad h) (g:=fun _=> f x) (fun y hy=>congrArg f hy),setIntegral_const,Measure.real,cell_area hp,ENNReal.toReal_ofReal (by positivity)]
    simp_rw [he] at e; exact e
lemma payment (hp:h>0) {f:Cover→E} (hi : Integrable (f ∘ pad h) volume) : Summable f := by
    have he :=  (Summable.const_smul (h^4)⁻¹ (throughput hp hi).summable)
    rw [show f = (fun i=> (h^4)⁻¹ • h^4 • f i) from funext fun i=>by rw [smul_smul,inv_mul_cancel₀ (pow_ne_zero 4 hp.ne'),one_smul]]; exact he
end YM.RG11Scheme.Mesh
