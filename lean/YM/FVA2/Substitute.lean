import YM.MS.Swirl.Sits
import YM.MS.Cylinder.Ink

/-!
# On changing the field alphabet in the finite calculation

Columns in substitution U send new fields/sources *into* old. Wick
composition works even for projections, degenerate covariance and odd lines.
-/

noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Substitute
open Matrix Function Set Finset MS MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal
open MS.Koszul MS.Bare MS.Book MS.Book.Convolve MS.Cylinder
open MS.Swirl MS.Puff MS.Puff.Engine MS.Puff.Actors MS.Puff.Mom
variable {X Y : Type} [Fintype X] (U : Matrix X Y ℂ)

def fieldChange : Raw X ℂ →ₗ[ℂ] Raw Y ℂ := lantern univ Uᵀ
scoped notation "ξ[" U "]" => fieldChange U

lemma asShade (F : Cyl X ℂ) : ξ[U] F.val = shade Uᵀ F :=
  (tinted Uᵀ F (s:=Finset.univ) (by simpa using Uses.entire F.val)).symm

lemma field_nil (F : Raw X ℂ) : ξ[U] F []=F [] := rfl
lemma field_D (F : Raw X ℂ) (y : Y) : D y (ξ[U] F) = ∑ x:X, U x y • ξ[U] (D x F) :=
  lantern_drop ..

lemma identity [DecidableEq X] (F : Raw X ℂ) : ξ[(1:Matrix X X ℂ)] F=F := by
  funext l; induction l generalizing F with
  | nil=> rfl
  | cons i l IH =>
    rw [D_eval i (fieldChange _ _),field_D,Finset.sum_eq_single_of_mem i (mem_univ _),
      Matrix.one_apply_eq,one_smul]; exact IH (D i F)
    intro x hx hi; rw [Matrix.one_apply_ne hi,zero_smul]

lemma comp_change [Fintype Y] {Z : Type} (V : Matrix Y Z ℂ) (F : Raw X ℂ) :
    ξ[V] (ξ[U] F) = ξ[U*V] F := by
  funext l; induction l generalizing F with
  | nil=> rfl
  | cons i l IH=>
    rw [D_eval i (fieldChange V _),D_eval i (fieldChange (U*V) _)]
    simp_rw [field_D,map_sum,map_smul,Finset.smul_sum,smul_smul,Finset.sum_apply,Pi.smul_apply]
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun x _ => ?_
    simp_rw [mul_apply, Finset.sum_smul, IH,mul_comm (V _ i)]

abbrev TieField (p : Sector X) (q : Sector Y) := Tie p q (Matrix.transpose U)

lemma constant (c : ℂ) : ξ[U] (coin c) = coin c :=
  (asShade U (piece c)).trans (coin_turn Uᵀ c)

lemma variable_form [Fintype Y] (x : X) : ξ[U] (atLetter x) = ∑ y:Y,U x y • atLetter y := by
  classical
  rw [show ξ[U] (atLetter x)=shade Uᵀ (Cylinder.single x) from asShade U (Cylinder.single x)]
  apply ext_D; · simp [Cylinder.single,atLetter]
  intro y; rw [names,map_sum]; simp_rw [map_smul]
  rw [Finset.sum_eq_single_of_mem y (mem_univ _), hear]; rfl
  intro z hz hy; rw [unheard _ (Ne.symm hy),smul_zero]

lemma in_rank (F : Raw X ℂ) (h : ℤ) : ξ[U] (mask h F) = mask h (ξ[U] F) := by
  rw [show ξ[U] F=shade Uᵀ (region.symm F) from asShade U (region.symm F)]
  rw [← mod_ink]; exact asShade U (model h (region.symm F))

lemma limit_change (F : Raw X ℂ) {n : ℤ} (H : Limit F n) : Limit (ξ[U] F) n := by
  rw [show ξ[U] F=shade Uᵀ (region.symm F) from asShade U (region.symm F)]; exact Limit.shades _ H _

variable {p : Sector X} {q : Sector Y} (h : TieField U p q)
include h
lemma pair_change (F G : Raw X ℂ) : ξ[U] (product p F G) = product q (ξ[U] F) (ξ[U] G) := by
  rw [show ξ[U] F=shade Uᵀ (region.symm F) from asShade U (region.symm F),show ξ[U] G=shade Uᵀ (region.symm G) from asShade U (region.symm G)]
  exact (asShade U (couple p (region.symm F) (region.symm G))).trans (h.prod _ _)

lemma tether : Tether ξ[U] (actor p) (actor q) := ⟨constant U 1,pair_change U h⟩
lemma exp_change (F : SpecB X) : promote ξ[U] (exp0 p F) = exp0 q (promote ξ[U] F) := by
  funext l; exact (tether U h).figure useN F l

lemma tether_marks {W : Type} [LinearOrder W] (L : Mate X W) (s : Finset W) :
    promote ξ[U] (Font p L s)= Font q ((promote ξ[U]) ∘ L) s :=
  ((tether U h).Extrapolation useN).figure _ L _
omit h

private lemma transpose_four {R S T X' E : Type} [Fintype R] [Fintype S] [Fintype T]
    [Fintype X'] [AddCommMonoid E] (f : R → S → T → X' → E) :
    (∑ i:R,∑ j:S,∑ k:T,∑ z:X', f i j k z) = ∑ k:T,∑ z:X',∑ j:S,∑ i:R,f i j k z := by
  rw [show (∑ i:R,∑ j:S,∑ k:T,∑ z:X', f i j k z)=
      ∑ j:S,∑ k:T,∑ z:X',∑ i:R,f i j k z from ?_]
  · nth_rw 1 [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  nth_rw 1 [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _ => ?_
  nth_rw 1 [Finset.sum_comm]; exact Finset.sum_congr rfl fun k _ => Finset.sum_comm

section Wick
variable [Fintype Y] (K : Matrix Y Y ℂ) (F : Raw X ℂ)

lemma frame_change : Cog.frame K (ξ[U] F) = ξ[U] (Cog.frame (U * K * Uᵀ) F) := by
  rw [fpΩ,fpΩ]
  simp_rw [diffPair_apply, field_D, map_sum,map_smul, field_D, Finset.smul_sum,smul_smul]
  rw [transpose_four]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp_rw [mul_apply, transpose_apply, Finset.sum_mul, Finset.sum_smul,mul_assoc]
  apply Finset.sum_congr rfl; intro x hx; simp_rw [mul_left_comm (U i _)]

lemma tep_change (i : ℕ) : tep K i (ξ[U] F) = ξ[U] (tep (U * K * Uᵀ) i F) := by
  induction i with
  | zero => rw [rise,rise]; rfl
  | succ i IH => rw [teen, teen, IH,map_smul, ← frame_change]

lemma view_change (hF : F ∈ Mini X) : View K (ξ[U] F)= View (U * K * Uᵀ) F := by
  obtain ⟨k,hk⟩ := hF
  change Shot _ _ [] = Shot _ _ []
  rw [dawn _ hk, dawn K (limit_change U F hk), effect]
  simp_rw [effect, LinearMap.sum_apply, tep_change, Finset.sum_apply, field_nil]
end Wick

section Real
open Cylinder.Taylor
open scoped Topology ContDiff
variable {E W : Type} [NormedAddCommGroup E] [NormedAddCommGroup W]
  [NormedSpace ℝ E] [NormedSpace ℝ W] (V : Matrix X Y ℝ)
  (e : X → E) (z : Y → W) (f : E → ℝ)

def intoC : Matrix X Y ℂ := V.map Complex.ofReal

lemma ink_along {f : E → ℝ} (H : germ f) :
    ξ[intoC V] (ink e f) = ink (fun y : Y=>∑ i:X,V i y • e i) f := by
  funext l; induction l generalizing f with
  | nil=> rfl
  | cons j l IH=>
    let u (y : Y) := ∑ i:X, V i y • e i
    rw [D_eval j (fieldChange _ _),field_D,Finset.sum_apply,D_eval j (ink _ _),inktip]
    have hLayer : layer (u j) f=∑ i:X,V i j • layer (e i) f := by
      funext a; rw [Finset.sum_apply]; unfold layer u; simp only [map_sum,map_smul,Pi.smul_apply]
    rw [show (∑ i:X,V i j • e i)=u j from rfl, hLayer,
      ink_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl; intro i _
    · rw [Pi.smul_apply, ink_smul _ (germ_layer H _), inktip]
      exact congr_arg ((V i j:ℂ) • ·) (IH (germ_layer H _))
    intro i _; exact (germ_layer H (e i)).const_smul (V i j)

lemma ink_change (L : W →L[ℝ] E) (hL : ∀ i,L (z i)=∑ j:X,V j i • e j) (H : germ f) :
    ξ[intoC V] (ink e f)=ink z (f ∘ L) := by rw [ink_along _ _ H, Taylor.tower _ _ L hL _ H]
end Real

end YM.FVA2.Substitute
