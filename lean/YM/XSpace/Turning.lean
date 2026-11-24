import YM.XSpace.LayoutShift
import YM.XSpace.Splinted
/-!
# Parity persistence during positioning

Positions far from Continuum exactly solved at regulators sufficiently
fine. The signed frame intertwines $J_0$, and all correl orders with
any slot filtration. Real labels and tests preserved.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Normalize
open Function Set Filter Maxwell Maxwell.Free Maxwell.Wick MeasureTheory PowerSeries Fray
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {d l n:ℕ} {A:Screen G d}

def Forward (R:Reports G d):= ∀ i:ℕ, recruit (hinge d) (R i)=((-1:ℝ)^i) • R i
def faced (T:Pick G d): Pick G d:= fun i=> ((-1:ℝ)^i) • arch d (T i)
lemma posing (T:Pick G d) (i:ℕ) (p:Sec G d): coeff i (deck T) (hinge d p)=((-1:ℝ)^i) • hinge d (coeff i (deck (faced T)) p):=by
  let a:ℝ:=(-1)^i
  rw [decked,decked]; by_cases hi:i=0
  · subst i; simp only [pulling, ↓reduceIte,faced,pow_zero, one_smul]; rw [stood_hinge,arches]
  simp only [pulling,if_neg hi,faced,Submodule.coe_smul_of_tower,LinearMap.smul_apply]; rw [show hinge d (a • _) = a • hinge d _ from map_smul ((hinge d (G:=G)).restrictScalars ℝ) _ _, arched,hinges_back, smul_smul]; unfold a; rw [← mul_pow, neg_one_mul,neg_neg,one_pow,one_smul]
lemma forward_layout (T:Pick G d) (R:Reports G d) (H:Forward R) (l:ℕ): recruit (hinge d) (realm (deck T) R l)=((-1:ℝ)^l) • realm (deck (faced T)) R l:=by
  ext1 n; ext1 t; ext1 p; change realm (deck T) R l n t (hinge d ∘ p)= ((-1:ℝ)^l) • realm (deck (faced T)) R l n t p
  rw [really,really,Finset.smul_sum]; refine Finset.sum_congr rfl fun i hi=>?_
  let a k:=(-1:ℝ)^k; let u j:= a (i (some j)); let v:= pulseU i (deck (faced T)) p; let y:= i none; let Q := R y n t
  have he (v: Fin n→Sec G d): Q (hinge d ∘ v)= a y • Q v := congr_arg (fun R:Prediction G d=> R n t v) (H y)
  have h: ∑ j : Option (Fin n), i j=l:= (totaled i).mp hi
  rw [Fintype.sum_option] at h; rw [show pulseU i (deck T) (hinge d ∘ p)=fun j=> u j • hinge d (v j) from funext fun j=> posing ..]
  change Q _= a l • Q v; rw [show Q (fun j=> u j • hinge d (v j))= (∏ j,u j) • Q (hinge d ∘ v) from (Q.restrictScalars ℝ).map_smul_univ u (hinge d ∘ v), he, smul_smul]
  unfold u a; rw [Finset.prod_pow_eq_pow_sum, mul_comm, ← pow_add,h]

def Respect (P:Reports G d):Prop:= ∀ i:ℕ, RealFields (P i)
lemma real_move (T:Pick G d) (P:Reports G d) (H: Respect P): Respect (realm (deck T) P):=by
  intro i n v t; rw [really,really, star_sum]; apply Finset.sum_congr rfl; intro a _; rw [← H _ _ _ _]; congr 1; funext j; simp only [Function.comp_apply,pulseU,decked,pulling]; split_ifs; exact (stood_reel ..).symm; exact (T _).property.2.2.1 _
lemma align_screen (h:A.Prepared): ∀ P:Prediction G d, recruit (hinge d) P=P → arch d (A.D P)=A.D P:= fun P H=> (h.2 P).symm.trans (congr_arg _ H)
lemma solve_arch (h:A.Prepared) (T:Pick G d) (R:Reports G d) (H:Forward R) (he:A.Solved T R): A.Solved (faced T) R:=by
  intro i; apply smul_right_injective (Change G d) (pow_ne_zero i (by norm_num : (-1:ℝ) ≠ 0))
  dsimp only; rw [← map_smul,← forward_layout T R H,h.2 _,he]; split_ifs with hi
  · subst i; rw [align_screen h _ (heredity _),pow_zero,one_smul]
  rw [map_zero,smul_zero]
lemma first_arch {P:Prediction G d} (h:A.Prepared) (T:Change G d) (he: recruit (hinge d) P=P) (hv:SetEq A T P) : SetEq A (arch d T) P := by
  unfold SetEq; rw [← show recruit (hinge d) (recruit (stand T) P)= recruit (stand (arch d T)) P from (reigns ..).trans (congr_arg _ he), h.2 _,hv,align_screen h _ (heredity _)]
end YM.XSpace.Normalize
