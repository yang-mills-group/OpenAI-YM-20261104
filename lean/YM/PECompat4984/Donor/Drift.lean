import YM.Extra.SOURCE_HISTORIES.Drift
import YM.Extra.SOURCE_HISTORIES.Play

/-! Exact seed helper restoration; retained definitions are imported unchanged. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories.Drift
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels Bid Motion
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}
variable (t : Site n)

lemma clean (p : BudgetPoint) (Y : Support n) (U : Config G n) :
    Healthy p.threshold (relocated t Y) U ↔ Healthy p.threshold Y (translate t U) := by
  rw [Healthy,Healthy,← flag]
  simp only [Finset.disjoint_iff_inter_eq_empty]
  unfold relocated; rw [← Finset.image_inter _ _ (add_left_injective t)]; simp only [Finset.image_eq_empty]

lemma keeps {P : Support n} {U V : Config G n} (h : Agrees (relocated t P) U V) :
    Agrees P (translate t U) (translate t V) := by
  rintro ⟨x,i⟩ hx hi
  refine h (x+t,i) ((through ..).1 hx) ?_
  change x+t+step i ∈ relocated t P
  rw [add_right_comm]; exact (through ..).1 hi

private lemma translated_gauge (x : Site n → G.El) (U : Config G n) :
    translate t (gauge x U) = gauge (x ∘ (·+t)) (translate t U) := by
  ext1 i
  simp only [Lattice.gauge,translate,comp_apply]; congr 3; abel

lemma gauge_kept {f : Config G n → ℂ} (h : GaugeInvariant f) : GaugeInvariant (f ∘ translate t) := by
  intro k U
  simp only [comp_apply, translated_gauge]; exact h _ _

lemma final_kept {f : Config G n → ℂ} {P : Support n} {u} (hr : UsesFinal u P f) :
    UsesFinal u (relocated t P) (f ∘ translate t) := by
  intro U V h hg
  refine hr _ _ (keeps t h) ?_
  rw [← flag t U,← flag t V] at hg
  unfold relocated at hg
  have hT := show Injective (·+t) from add_left_injective t
  rw [← Finset.image_inter _ _ hT, ← Finset.image_inter _ _ hT] at hg
  exact Finset.image_injective hT hg

lemma test_translate (A : Hol G) (o : Site n) (J : Jet G) (d : ℕ) (r : ℝ) :
    translate t (A.testLinks d (o+t) J r)= A.testLinks d o J r := by
  ext1 i; simp [translate, Hol.testLinks]

lemma nonwrap {P : Support n} {o : Site n} (h : Nonwrapping (relocated t P) (o+t)) : Nonwrapping P o := by
  intro x hx
  simpa only [separation_translate] using h (x+t) ((through ..).1 hx)


lemma shift_inc (U : Config G n) (v : Directions G n) :
    translate t (increment U v) = increment (translate t U) (directions t v) := rfl

lemma local_series (f : Config G n → ℂ) (l : List (Directions G n)) (U) :
    leftDerivs (f ∘ translate t) l U = leftDerivs f (l.map (directions t)) (translate t U) := by
  induction l generalizing U with
  | nil => rfl
  | cons a l ih => simp_rw [leftDerivs,ih, shift_inc, map_smul,List.map_cons,leftDerivs]

lemma translate_cont : Continuous (translate t (K:=G.El)) := by unfold translate; fun_prop

lemma regular_kept {p : BudgetPoint} {Y : Support n} {f : Config G n → ℂ} (h : p.Regular Y f) :
    p.Regular (relocated t Y) (f ∘ translate t) := by
  have ht (U : Config G n) (he : Healthy p.threshold (relocated t Y) U) : ContDiffAt ℝ (p.order:WithTop ℕ∞)
      ((f ∘ translate t) ∘ increment U) 0 := by
    have hg := h.smooth (translate t U) ((clean ..).1 he)
    let D := directions t (G:=G)
    exact (show ContDiffAt ℝ (p.order:WithTop ℕ∞) _ (D 0) from (map_zero D).symm ▸ hg).comp _
      D.toContinuousLinearMap.contDiff.contDiffAt
  refine ⟨fun U V hh => h.sites _ _ (keeps t hh), h.borel.comp (translate_cont t).measurable,
    gauge_kept t h.symmetry,ht,fun U he a l h => ?_⟩
  exact Next.Foundations.left_has a h (ht U he)

lemma bounds_kept {p : BudgetPoint} {Y : Support n} {f : Config G n → ℂ} {o c} (h : p.supBounds o Y f c) :
    p.supBounds (o+t) (relocated t Y) (f ∘ translate t) c := by
  refine ⟨h.1,fun U hu l hh hd => ?_⟩
  rw [local_series]
  apply h.2 _ ((clean ..).1 hu) _ (by simpa using hh)
  intro a ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  intro i
  simpa only [directions,LinearMap.coe_mk, AddHom.coe_mk,separation_translate] using hd b hb (i.1+t,i.2)

lemma reloc_foot (B : SectionData F) (o : Site n) : relocated t (B.footprint o) = B.footprint (o+t) := by
  simp only [relocated,SectionData.footprint, Finset.image_image,comp_def,add_assoc]

end YM.Extra.Histories.Drift
end
