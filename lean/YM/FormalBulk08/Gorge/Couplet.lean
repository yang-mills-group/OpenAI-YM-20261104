import YM.FormalBulk08.Gorge.Ladle

/-! Wiring estimate, no loss of width in displacements at contractions. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Gorge
open Lava Function Wick
open scoped BigOperators Classical ENNReal
variable {V : Type*} {σ : ℝ} {m n : ℕ}

def arm (v : chain V (m+n)) (a : V) : chain V (m+1) := Fin.cons a (v ∘ Fin.castAdd n)
def leg (v : chain V (m+n)) (a : V) : chain V (n+1):= Fin.cons a (v ∘ Fin.natAdd m)
lemma legs_wide (D : Reach V) (v : chain V (m+n)) (a b : V) : wide D v ≤ wide D (arm v a)+wide D (leg v b)+D.d a b := by
   have h i j : D.d (v (Fin.castAdd n i)) (v (Fin.natAdd m j)) ≤ wide D (arm v a)+wide D (leg v b)+D.d a b := by
      have e := D.tri (v (Fin.castAdd n i)) a b; have f:=D.tri (v (Fin.castAdd n i)) b (v (Fin.natAdd m j)); have hv:=reached D (arm v a) i.succ 0; have hi:=reached D (leg v b) 0 j.succ;simp only [arm,leg,Fin.cons_succ,comp_apply,Fin.cons_zero] at *; omega
   apply known_wide; intro i j
   cases i using Fin.addCases with
   | left i =>
      cases j using Fin.addCases with
      | left j =>
         have hh:=reached D (arm v a) i.succ j.succ; simp only [arm, Fin.cons_succ,comp_apply] at *;omega
      | right j=> exact h i j
   | right i=>
      cases j using Fin.addCases with
      | left j=> rw [D.turn]; exact h j i
      | right j=> have hh:=reached D (leg v b) i.succ j.succ; simp only [leg,Fin.cons_succ, comp_apply] at *;omega

def Grate (D : Reach V) (σ : ℝ) (q : V→V→ℝ) (B : ℝ) := 0 ≤ B ∧ ∀ a, (∑' b, shine σ (D.d a b)*‖q a b‖ₑ) ≤ ENNReal.ofReal B
lemma Grate.rough {D : Reach V} {q : V→ V→ℝ} {B : ℝ} (h : Grate D σ q B) (hs : 0≤σ) (a b) : |q a b| ≤ B := by
   have he : ‖q a b‖ₑ ≤ ENNReal.ofReal B:= (le_mul_of_one_le_left' (shine_plus _ hs _)).trans ((ENNReal.le_tsum (f:=fun b=>shine σ (D.d a b)*‖q a b‖ₑ) b).trans (h.2 a))
   rw [←ofReal_norm] at he; exact (ENNReal.ofReal_le_ofReal_iff h.1).mp he
lemma Grate.turn {D : Reach V} {q : V→ V→ℝ} {B : ℝ} (h : Grate D σ q B) (hx : ∀ i j, q i j = q j i) : Grate D σ (fun i j=> q j i) B := by rwa [show (fun i j=> q j i) = q by ext i j; rw [hx]]

-- for sums with root held in left
lemma counted_cast {Q : (chain V m) → V→ ℝ≥0∞} {W : V→chain V n→ℝ≥0∞} (i : Fin m) (x : V) (L : V → V→ℝ≥0∞) (A B C : ℝ≥0∞)
   (he : (∑' v : pack i x,∑' a,Q v.val a) ≤ A)
   (hh : ∀ b,(∑' t,W b t) ≤ B) (hr : ∀ a,(∑' b,L a b) ≤ C) :
   (∑' u : pack (Fin.castAdd n i) x,∑' j : V×V,Q (u.val ∘ Fin.castAdd n) j.1*W j.2 (u.val ∘ Fin.natAdd m)*L j.1 j.2) ≤ A*(B*C) := by
   let f : pack (Fin.castAdd n i) x → pack i x × chain V n := fun u=> (⟨u.val ∘ Fin.castAdd n,u.property⟩,u.val ∘ Fin.natAdd m)
   let g (v : pack i x × chain V n) := ∑' j : V×V,Q v.1.val j.1 * W j.2 v.2 * L j.1 j.2
   have hx : Injective f:= fun v w h=> Subtype.ext (funext fun j=> Fin.addCases (fun k=>congr_fun (congr_arg (Subtype.val ∘ Prod.fst) h) k) (fun k=>congr_fun (congr_arg Prod.snd h) k) j)
   refine (ENNReal.tsum_comp_le_tsum_of_injective hx g).trans ?_; refine le_trans ?_ (mul_le_mul_left he (B*C)); rw [ENNReal.tsum_prod', ← ENNReal.tsum_mul_right]; refine ENNReal.tsum_le_tsum fun v=>?_ ;
   unfold g; rw [←ENNReal.tsum_mul_right, ENNReal.tsum_comm]; rw [ENNReal.tsum_prod']; dsimp only
   refine ENNReal.tsum_le_tsum fun a=>?_
   refine le_trans ?_ (mul_le_mul_right (mul_le_mul_right (hr a) B) (Q v.val a)); rw [mul_comm B,←ENNReal.tsum_mul_right,←ENNReal.tsum_mul_left]; refine ENNReal.tsum_le_tsum fun b=>?_
   rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]; rw [mul_comm (L a b),←mul_assoc]; gcongr; apply hh

-- Trop terms
variable (D : Reach V) (q : V→V→ℝ)
def weld (T : Tile V (m+1)) (S : Tile V (n+1)) (v : chain V (m+n)) (a : V×V) := halve (q a.1 a.2) * ((m+1:ℕ):ℝ) * ((n+1:ℕ):ℝ) * clutch (shed T a.1) (shed S a.2) v
lemma joint_pay (T : Tile V (m+1)) (S : Tile V (n+1)) (v : chain V (m+n)) (a : V×V) (hs : 0≤σ):
    shine σ (wide D v)*‖weld q T S v a‖ₑ ≤ ENNReal.ofReal (1/2*(m+1)*(n+1)) * (glitter D σ T (arm v a.1)*glitter D σ S (leg v a.2)*(shine σ (D.d a.1 a.2)* ‖q a.1 a.2‖ₑ)) := by
   have hp : weld q T S v a=(1/2*(m+1)*(n+1))*q a.1 a.2*T (arm v a.1)* S (leg v a.2) := by unfold weld halve clutch shed leg arm;simp; ring
   refine (mul_le_mul_left (shine_le _ hs (legs_wide D v a.1 a.2)) _).trans (le_of_eq ?_)
   rw [hp,enorm_mul,enorm_mul,enorm_mul,shine_add,shine_add,glitter,glitter]
   let N : ℝ:=1/2*(m+1)*(n+1);rw [← ofReal_norm _, Real.norm_eq_abs, abs_of_nonneg (show 0≤1/2*((m:ℝ)+1)*((n:ℝ)+1) by positivity)]; ring
end YM.FormalBulk08.Gorge
