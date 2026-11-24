import YM.PertExtension.BareChart
import YM.Work.F05.Transport
import YM.Work.F05.Reindex

/-!
Forest expenditure, with actual Haar. This version simply proves the push
of `prior` onto the slice (rather than allowing any confusion on restricting
to a slice which may be of positive codimension). Exact for arbitrary root-gauge
respecting weights. No measurability required beyond indicated. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Volume
open Filter Function MeasureTheory Set Lattice Exterior Tree Wilson RG Precision Profiles
open scoped Topology Classical Matrix.Norms.Frobenius BigOperators ContDiff ENNReal

variable {G : Gauge}{c f : Side}{S : StepData c f}{g : Ratio c f} (T : Forest g)

theorem rooted : MeasurePreserving (Profiles.wick (G:=G) T) (prior G f) (T.order G) := by
   refine ⟨(continuous_wick T).measurable,?_⟩
   ext X hX
   let B := X.indicator fun _=> (1:ℝ)
   let Y := wick T ⁻¹' X
   let F := B ∘ wick T
   have hm : MeasurableSet Y := (continuous_wick T).measurable hX
   have he : F = Y.indicator fun _ => (1:ℝ) := by unfold F B Y; funext i; by_cases h:wick T i∈X <;> simp [h]
   have ht : Integrable F (prior G f) := by rw [he]; exact (integrable_const _).indicator hm
   have hr : ∀ k : Site f → G.El, (∀ i, k (g.embed i)=1)→ ∀ x,F (Lattice.gauge k x)= F x := fun k hv x=> congr_arg B (wick_gauge T x k hv)
   have hw := T.pack F ht hr
   rw [Measure.map_apply (continuous_wick T).measurable hX]
   nth_rw 1 [he,integral_indicator hm,setIntegral_const] at hw
   simp_rw [F,Function.comp_apply,Profiles.wick_root,B] at hw
   rw [integral_indicator hX, setIntegral_const] at hw
   exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp (by simpa only [Y,smul_eq_mul,mul_one] using! hw)

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

-- Variant on roots rather than all-site invariance.
def Fundamental (F : Config G f→ X) := ∀ k : Site f→G.El,(∀ x,k (g.embed x)=1)→ ∀ x,F (Lattice.gauge k x)=F x

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
lemma attends (F : Config G f→ X) (h : Fundamental (g:=g) F) :
    (F ∘ T.drape) ∘ wick T = F := funext fun x=>by
   change F (T.drape (wick T x))=F x; rw [wears T]; exact h (T.foldAt x) (fun _=> T.fold_root ..) _

section on_slice
variable {F : Config G f→ ℂ}(h : Fundamental (g:=g) F)(hm : Measurable F)
include h hm
lemma to_slice : (∫ x,F x ∂prior G f)=∫ y, F (T.drape y) ∂T.order G := by
   rw [← (rooted T).map_eq]
   symm
   exact (integral_map (f:=F ∘ T.drape) (continuous_wick ..).measurable.aemeasurable (hm.comp (Forest.continuous_drape T).measurable).aestronglyMeasurable).trans (integral_congr_ae <| Eventually.of_forall (congr_fun (attends T F h)))
lemma integral_right : Integrable F (prior G f) ↔ Integrable (fun x=>F (T.drape x)) (T.order G) := by
   have he := attends T F h
   symm
   rw [← (rooted T).map_eq]
   exact (integrable_map_measure (g:=F ∘ T.drape) (hm.comp T.continuous_drape.measurable).aestronglyMeasurable (continuous_wick ..).measurable.aemeasurable).trans (by rw [he])
lemma to_slice_on (B : Set (T.Slice G))(H : MeasurableSet B) :
    (∫ x in wick T ⁻¹' B,F x ∂prior G f) = ∫ y in B,F (T.drape y) ∂T.order G := by
   rw [← integral_indicator ((continuous_wick T).measurable H),←integral_indicator H]
   rw [to_slice T]; apply integral_congr_ae (Eventually.of_forall _)
   · intro x; by_cases he : x∈B <;> simp [he,wick_root]
   · intro k he x; by_cases hx : wick T x∈ B <;> simp [wick_gauge T x k he,hx,h k he]
   exact hm.indicator ((continuous_wick T).measurable H)
lemma on_right (B : Set (T.Slice G))(H : MeasurableSet B) :
    IntegrableOn F (wick T ⁻¹' B) (prior G f) ↔ IntegrableOn (F ∘ T.drape) B (T.order G) := by
   rw [← integrable_indicator_iff H, ← integrable_indicator_iff ((continuous_wick T).measurable H),integral_right T]
   · rw [show (fun x => (wick T ⁻¹' B).indicator F (T.drape x))=B.indicator (F ∘ T.drape) from funext fun x=> by by_cases h:x∈B <;> simp [wick_root,h]]
   · intro k he x; by_cases hx : wick T x∈B <;> simp [wick_gauge T x k he,hx,h k he]
   exact hm.indicator ((continuous_wick T).measurable H)
end on_slice
end YM.RG02.Volume
