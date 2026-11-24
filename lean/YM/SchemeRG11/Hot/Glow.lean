import YM.SchemeRG11.Hot.Veil
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
/-!
Individual dimensionally prescribed Schwinger times. Open-index positions of any
finite ranks. `word` reads external position derivatives; applies also to the
heat differentiation used when dressing a B-pole of a density vertex.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.SchemeRG11.Hot
open Function Set MeasureTheory Filter Metric Asymptotics MSbar
open scoped Topology ContDiff BigOperators

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
variable {n : ℕ}

def ray (i : Fin n) : Space n := EuclideanSpace.single i 1

def fog (μ : ℝ) (t : ℝ) (e : ℂ) (x : Space n) := Pole.factor μ e*(t:ℂ)^(e-2)*(Real.exp (-t⁻¹*(‖x‖^2/4)):ℝ)

def plume (μ : ℝ) (l : List (Fin n)) (t : ℝ) (e : ℂ) : Space n→ℂ := series (fog μ t e) (l.map ray)

/-- A function represented for *positive* heat time only. -/
def Hearth (F : ℝ→ℂ→Space n→ℂ) := ∃ P : Tint Unit (Space n), ∀ t : ℝ, 0<t → ∀ e, F t e=tongs (fun _ x=> ‖x‖^2/4) P t (fun _=> t⁻¹) e

lemma hemp {μ : ℝ} (h : 0<μ) (l : List (Fin n)) : Hearth (plume μ l) := by
  let P : Tint Unit (Space n):=Tint.number (Pole.factor μ) (Pole.factor_entire μ h)
  let φ := fun (_ : Unit) (x : Space n)=> ‖x‖^2/4
  have he t e : fog μ t e (n:=n) = tongs φ P t (fun _=> t⁻¹) e := by ext1 x; simp only [fog,tongs,Fintype.sum_unique,φ,P,Tint.read]; simp only [neg_mul]; ring
  obtain ⟨Q,hQ⟩:=recast (P:=P) (l:=l.map ray) (φ:=φ) (fun _=> (contDiff_norm_sq ℝ).div_const _)
  exact ⟨Q,fun t _ e=> by rw [plume,he,hQ]⟩

def ember (F : ℝ→ℂ→Space n→ℂ) (t : ℝ) (e : ℂ) (x : Space n) := deriv (fun t : ℝ=> F t e x) t

namespace Hearth
variable {F : ℝ→ℂ→Space n→ℂ}
private lemma iscr : ∀ _ : Unit, ContDiff ℝ ∞ (fun x : Space n=> ‖x‖^2/4) := fun _=> (contDiff_norm_sq ℝ).div_const _

lemma fires (h : Hearth F) : ∃ G : ℝ→ℂ→Space n→ℂ, Hearth G ∧
    ∀ (t : ℝ), 0<t → ∀ e x, HasDerivAt (fun t : ℝ=>F t e x) (G t e x) t := by
  obtain ⟨P,h⟩:=h; obtain ⟨Q,k⟩:=swath P (iscr (n:=n))
  refine ⟨fun t e=>tongs _ Q t (fun _=> t⁻¹) e,⟨Q,fun _ _ _=> rfl⟩,fun t ht e x=>?_⟩
  apply (k t ht e x).congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with r hr
  rw [h r hr]
lemma coals (h : Hearth F) : Hearth (ember F) := by
  obtain ⟨G,⟨P,k⟩,e⟩:=h.fires
  exact ⟨P,fun t ht y=> (funext fun x=> (e t ht y x).deriv).trans (k t ht y)⟩
lemma slope (h : Hearth F) {t : ℝ} (ht : 0<t) (e x) : HasDerivAt (fun t : ℝ=>F t e x) (ember F t e x) t := by
  obtain ⟨G,-,k⟩:=h.fires; rw [ember,(k t ht e x).deriv]; exact k t ht e x

lemma spark {Y : Type} [TopologicalSpace Y] (h : Hearth F) {t : Y→ℝ} {e : Y→ℂ} {x : Y→Space n} {y : Y} (ht : ContinuousAt t y) (he : ContinuousAt e y) (hx : ContinuousAt x y) (hT : 0<t y) :
    ContinuousAt (fun y=> F (t y) (e y) (x y)) y := by
  obtain ⟨P,k⟩:=h
  refine (tackle (fun i => (iscr (n:=n) i).continuous) P ht (r:=fun y (_ : Unit)=> (t y)⁻¹) ?_ he hx hT.ne').congr ?_
  · exact continuousAt_pi.mpr (fun _=> ht.inv₀ hT.ne')
  filter_upwards [ht.eventually (lt_mem_nhds hT)] with b hb; exact (congr_fun (k _ hb _) _).symm
lemma holds (h : Hearth F) {t : ℝ} (ht : 0<t) (x : Space n) : Differentiable ℂ (fun e=> F t e x) := by
  obtain ⟨P,k⟩:=h; simp only [k t ht]
  exact tunnel _ _ ht _ _

private lemma clearance {K : Set (Space n)} (hk : IsCompact K) (hu : 0 ∉ K) : ∃ c>0, ∀ x∈K,c ≤ ‖x‖^2/4 := by
  by_cases he : K.Nonempty
  · obtain ⟨b,hb,hB⟩:=hk.exists_isMinOn he (f:=fun x=> ‖x‖^2/4) (iscr (n:=n) ()).continuous.continuousOn
    exact ⟨‖b‖^2/4, div_pos (pow_pos (norm_pos_iff.mpr (fun h=> hu (h ▸ hb))) _) (by norm_num), fun x hx=> hB hx⟩
  exact ⟨1,zero_lt_one,fun x hx=> False.elim (he ⟨x,hx⟩)⟩

lemma globule (h : Hearth F) {K : Set (Space n)} (hk : IsCompact K) (hl : 0∉K) {U : Set ℂ} (hu : IsCompact U) (B : ℝ) :
    ∃ C>0, ∀ e∈U, ∀ x∈K, ∀ t∈Ioc 0 B, ‖F t e x‖ ≤ C := by
  obtain ⟨c,hc,h'⟩ := clearance hk hl
  obtain ⟨P,k⟩:=h
  obtain ⟨C,hC,e⟩:=respite P (φ:=fun _ x=> ‖x‖^2/4) hc hu hk h' B
  exact ⟨C,hC,fun y hy x hx r hr=> by rw [k r hr.1]; exact e y hy x hx r hr⟩

def coat (t : ℝ) := (1+t)⁻¹^2
lemma medal (h : Hearth F) {K : Set (Space n)} (hk : IsCompact K) (hl : 0∉K) :
    ∃ C>0, ∀ x∈K, ∀ t>0, ‖F t 0 x‖ ≤ C*coat t := by
  obtain ⟨c,hc,h'⟩:=clearance hk hl
  obtain ⟨P,k⟩:=h
  obtain ⟨C,hC,e⟩:=mist P (φ:=fun _ x=> ‖x‖^2/4) hc hk h'
  exact ⟨C,hC,fun x hx t ht=> by rw [k t ht]; exact e x hx t ht⟩
lemma pay_coat : IntegrableOn coat (Ioi 0) := by
  have h : Integrable (fun t:ℝ=> (1+‖t‖)^(-(2:ℝ))) := integrable_one_add_norm (by norm_num)
  refine h.integrableOn.congr_fun ?_ measurableSet_Ioi
  intro x hx
  change (1+‖x‖)^(-(2:ℝ))=coat x
  rw [Real.norm_of_nonneg (show 0≤x from le_of_lt hx),Real.rpow_neg (by have hx : 0<x:=hx; positivity),Real.rpow_two,coat,inv_pow]
lemma coat_le {t u : ℝ} (hu : 0<u) (h : u≤t) : coat t ≤ coat u := by have ht := hu.trans_le h; unfold coat; gcongr
lemma soluble (h : Hearth F) {x : Space n} (hx : x≠0) : IntegrableOn (fun t=> F t 0 x) (Ioi 0) := by
  obtain ⟨C,hC,e⟩:=h.medal isCompact_singleton (show 0 ∉ ({x}:Set (Space n)) from fun H=> hx ((mem_singleton_iff.mp H).symm))
  exact Integrable.mono' (pay_coat.const_mul C)
    ((ContinuousOn.aestronglyMeasurable (fun t (ht : t ∈ Ioi 0)=> (h.spark (t:=id) continuousAt_id continuousAt_const continuousAt_const (show 0 < id t from ht)).continuousWithinAt)) measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht=> e x rfl t ht))
end Hearth
end YM.SchemeRG11.Hot
