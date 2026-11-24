import YM.XSpace.Traversing
import Mathlib.Algebra.Module.Submodule.Union

/-!
# Null path through any two points. Avoid ALL spectators.

Path of middle vertex in bilocal-generation. Analytic continuation at +i has
no edge to the interior spectators.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Traverse
open Function Set Filter Tensor Maxwell Maxwell.Free
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {v u c x y : E4}
def Normal (v:E4) := (Submodule.span ℝ ({v}:Set E4))ᗮ
lemma N_iff (u v : E4) : u ∈ Normal v ↔ ⟪v,u⟫=0:= Submodule.mem_orthogonal_singleton_iff_inner_right
structure Wheel (v u : E4) : Prop where
  starts : v≠0
  cross : ⟪v,u⟫=0
  axis : ‖u‖=‖v‖
lemma Wheel.runs (H : Wheel v u) : u≠0:= norm_pos_iff.mp (H.axis.symm ▸ norm_pos_iff.mpr H.starts)
lemma Wheel.back (H : Wheel v u) : Wheel (-v) u:=⟨by simp [H.starts], by rw [inner_neg_left,H.cross,neg_zero], by rw [norm_neg,H.axis]⟩
lemma Wheel.spoke (H : Wheel v u) : jump (interval v u)=0:=by rw [jumps,H.axis,H.cross]; simp
lemma bad_circle (hv : ‖v‖=‖u‖) : jump (interval x u)=0 ↔ ‖x‖=‖v‖ ∧ ⟪x,u⟫=0:=by
  rw [jumps]; constructor
  · intro h; have he:= congr_arg Complex.re h; have hh:= congr_arg Complex.im h; simp only [Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im, Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.zero_re,Complex.zero_im,Complex.I_re,Complex.I_im] at he hh; exact ⟨by rw [hv]; nlinarith [norm_nonneg x,norm_nonneg u], by linarith⟩
  rintro ⟨h,h'⟩; rw [h,hv,h']; simp

lemma N_not_inside (hv : v≠0) (gx : ‖x‖=‖v‖) (ep : x≠v) (eq : x≠-v) : ¬ Normal v ≤ Normal x:=by
  intro h
  have hh : x ∈ (Normal v)ᗮ := Submodule.orthogonal_le h ( (Submodule.span ℝ ({x}:Set E4)).le_orthogonal_orthogonal (Submodule.subset_span (show x∈({x}:Set E4) from rfl)))
  rw [Normal,Submodule.orthogonal_orthogonal] at hh; obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hh
  rw [norm_smul,Real.norm_eq_abs] at gx; rw [abs_eq_max_neg] at gx
  have hc := norm_pos_iff.mpr hv
  rcases le_total (-a) a with h|h
  · rw [max_eq_left h] at gx; apply ep; rw [show a=1 by nlinarith,one_smul]
  rw [max_eq_right h] at gx; apply eq; rw [show a= -1 by nlinarith,neg_one_smul]

lemma directions (S : Finset E4) (hv : v≠0) (ha : c-v ∉ S) (hb : c+v∉ S) : ∃ u : E4, Wheel v u ∧ ∀ x∈S, jump (interval (c-x) u)≠0:=by
  classical
  let N:= Normal v
  let B (x : E4) := (Normal (c-x)).comap N.subtype
  have hh x (hx:x∈S) (he : ‖c-x‖=‖v‖): B x ≠ ⊤:=by
    intro h; apply N_not_inside hv he (fun e => ha (by rw [← e,sub_sub_self]; exact hx)) (fun e => hb (by  rw [show c+v=x from by rw [← neg_neg v,← e]; abel]; exact hx))
    intro u hu; let w:N:=⟨u,hu⟩; exact (show w∈B x from h.symm ▸ Submodule.mem_top)
  let Z : Option E4 → Submodule ℝ N := Option.elim' ⊥ fun x=> if x∈S ∧ ‖c-x‖=‖v‖ then B x else ⊥
  have hi : 0 < Module.finrank ℝ N:=by
    unfold N Normal; have h:= (Submodule.span ℝ ({v}:Set E4)).finrank_add_finrank_orthogonal
    rw [finrank_euclideanSpace, Fintype.card_fin, finrank_span_singleton hv] at h; omega
  letI : Nontrivial N:= Module.nontrivial_of_finrank_pos hi
  have hZ : ∀ x,Z x≠ ⊤:= fun x=> Option.recOn x bot_ne_top (fun x=>by change ite _ _ (_:Submodule ℝ N)≠ ⊤; split_ifs with h; exact hh x h.1 h.2; exact bot_ne_top)
  let E := insert none (S.image Option.some)
  obtain ⟨x,-,hx⟩:= Set.exists_of_ssubset (Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt E Z hZ (by simp))
  have ht (y) (hy:y∈E): x ∉ Z y:=fun h=>hx (Set.mem_iUnion.mpr ⟨y,Set.mem_iUnion.mpr ⟨hy,h⟩⟩)
  let W:= (x.val:E4); have hW : W≠0:=fun h=> ht none (by simp [E]) (show x∈(⊥:Submodule ℝ N) from (Submodule.mem_bot ..).mpr (Subtype.ext h))
  let r := ‖v‖ / ‖W‖; have hr : 0<r:= div_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hW)
  have hs : ‖r • W‖=‖v‖:=by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]; exact div_mul_cancel₀ _ (norm_pos_iff.mpr hW).ne'
  refine ⟨_,⟨hv,(N_iff ..).mp (N.smul_mem r x.property),hs⟩,fun y hy e=>?_⟩
  obtain ⟨hz,h⟩:=(bad_circle hs.symm).mp e; apply ht (some y) (by simp [E,hy]); simp only [Z,Option.elim'_some, hy,hz,and_self, ↓reduceIte]; change W∈ Normal _
  rw [real_inner_smul_right] at h; exact (N_iff ..).mpr ((mul_eq_zero.mp h).resolve_left hr.ne')

lemma rolling (H : Wheel v u) (c x : E4) : ∀ᶠ t in atTop, course c u t ≠ x:=by
  have h:(fun t=> course c u t-x)=(fun t=> course (c-x) u t):=by funext; unfold course; abel
  filter_upwards [sliding (v:=c-x) H.runs] with t ht; exact sub_ne_zero.mp ((congr_fun h t).symm ▸ ht)
end YM.XSpace.Traverse
