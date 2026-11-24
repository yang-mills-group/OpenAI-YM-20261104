import YM.WilsonCoeffUV.Series.Components.TensorPolynomial
import YM.WilsonCoeffUV.Series.FormalWick
/-!
# `e,h,r` component heat recursion

Natural degrees. Coupling order e, aux. polynomial time h, external potential
arity r. No mark join at unchanged scalar grade. Marked readout may start at
coupling degree zero and values in a real module (addresses later); normalization
inserts both terms, even for nonsymmetric numerator.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue
open Matrix Function Finset
open scoped BigOperators
variable {U R: Type*} [Fintype U] [AddCommGroup R] [Module ℝ R]

/-- Index h outside e (compute without circularity). -/
abbrev Layers (R U:Type*):= ℕ → ℕ → Gen R U

def ravel (G:Matrix U U ℝ)(P:Layers ℝ U)(Q:Layers R U)(h e:ℕ):Gen R U :=
    ∑ i∈antidiagonal h,∑ j∈antidiagonal e, arbor G (P i.1 j.1) (Q i.2 j.2)

noncomputable def abr (G:Matrix U U ℝ)(P:ℕ→ Gen ℝ U) (h e:ℕ) : Gen ℝ U := match h with
| 0=> P e
| k+1 => ((k+1:ℕ):ℝ)⁻¹ • (ripple G (abr G P k e)+ravel G (fun j i=>if _h:j≤k then abr G P j i else 0) (fun j i=>if _h:j≤k then abr G P j i else 0) k e)
termination_by h

noncomputable def bul (G:Matrix U U ℝ)(D:Layers ℝ U)(P:ℕ→Gen R U)(h e:ℕ):Gen R U:= match h with
| 0 => P e
| k+1 => ((k+1:ℕ):ℝ)⁻¹ • (ripple G (bul G D P k e)+ravel G D (fun j i=>if _h:j≤k then bul G D P j i else 0) k e + ravel G.transpose D (fun j i=>if _h:j≤k then bul G D P j i else 0) k e)
termination_by h

lemma abr_zero (G:Matrix U U ℝ)(P:ℕ→ Gen ℝ U)(e) : abr G P 0 e=P e := by rw [abr]
lemma ravel_eq (G:Matrix U U ℝ)(P Q: Layers ℝ U)(A B:Layers R U){e k}
    (h:∀ j≤k,∀ i≤e,P j i=Q j i)(w:∀ j≤k,∀ i≤e,A j i=B j i) : ravel G P A k e=ravel G Q B k e := by
  apply sum_congr rfl; intro i hi; apply sum_congr rfl; intro j hj
  have he : i.1+i.2=k := mem_antidiagonal.mp hi; have ht : j.1+j.2=e := mem_antidiagonal.mp hj
  rw [h i.1 (by omega) j.1 (by omega), w i.2 (by omega) j.2 (by omega)]
lemma abr_next (G:Matrix U U ℝ)(P:ℕ→ Gen ℝ U)(k e) : abr G P (k+1) e=((k+1:ℕ):ℝ)⁻¹ • (ripple G (abr G P k e)+ravel G (abr G P) (abr G P) k e) := by
  rw [abr]; let A:=fun j i=>if _h:j≤k then abr G P j i else 0
  have ht (i) (hi : i≤k)(j) (_:j≤e) : A i j=abr G P i j:=dif_pos hi
  rw [ravel_eq G A (abr G P) A (abr G P) ht ht]
lemma bul_zero (G:Matrix U U ℝ)(D:Layers ℝ U)(P:ℕ→Gen R U)(e) : bul G D P 0 e=P e := by rw [bul]
lemma bul_next (G:Matrix U U ℝ)(D:Layers ℝ U)(P:ℕ→Gen R U)(k e): bul G D P (k+1) e=((k+1:ℕ):ℝ)⁻¹ •
     (ripple G (bul G D P k e)+ravel G D (bul G D P) k e + ravel G.transpose D (bul G D P) k e) := by
  rw [bul];
  have h (H:Matrix U U ℝ) := ravel_eq H D D (fun j i=>if _h:j≤k then bul G D P j i else 0) (bul G D P) (k:=k) (e:=e) (fun _ _ _ _=>rfl) (fun i hi j _=> dif_pos hi)
  rw [h,h]
lemma pure_ravel (G:Matrix U U ℝ)(P:Layers ℝ U)(Q:Layers R U)(h e : ℕ) : Pure (ravel G P Q h e) := by
  intro r; simp_rw [ravel,Finset.sum_apply]; exact Smooth.sum fun i _=>Smooth.sum fun j _=>arbor_pure G _ _ r
lemma pure_abr (G:Matrix U U ℝ){P:ℕ→Gen ℝ U}(p:∀ e,Pure (P e))(h e : ℕ) : Pure (abr G P h e) := by
  induction h with
  | zero=> rw [abr]; exact p e
  | succ n ih=> rw [abr_next]; intro r; simp_rw [Pi.smul_apply,Pi.add_apply]; exact ((pure_ripple G ih r).add (pure_ravel G _ _ _ _ r)).smul _
lemma pure_bul (G:Matrix U U ℝ)(D:Layers ℝ U){P:ℕ→Gen R U}(p:∀ e,Pure (P e))(h e :ℕ) : Pure (bul G D P h e) := by
  induction h with
  | zero=> rw [bul]; exact p e
  | succ n ih=> rw [bul_next]; exact fun r=>(((pure_ripple G ih r).add (pure_ravel G _ _ _ _ r)).add (pure_ravel G.transpose _ _ _ _ r)).smul _
lemma ravel_zero (G:Matrix U U ℝ){P:Layers ℝ U}{Q:Layers R U}{h e r : ℕ}(p:∀ a b x y i j:ℕ, a+b=h→x+y=e→i+j=r→ P a x (i+1)=0 ∨ Q b y (j+1)=0) : ravel G P Q h e r=0 := by
  simp_rw [ravel,Finset.sum_apply]; apply sum_eq_zero; intro i hi; apply sum_eq_zero; intro j hj
  exact arbor_zero_at G _ _ _ fun _ _ hk=> p _ _ _ _ _ _ (mem_antidiagonal.mp hi) (mem_antidiagonal.mp hj) hk

/-! Finite profiles. `l`: order-zero source field bound (`<=`). -/
def shellK (l:ℕ)(P:ℕ→ Gen R U) : Prop := ∀ k r,r>l+k → P k r=0
def stops (l:ℕ)(P:Layers R U): Prop := ∀ h e r,r>l+e ∨ r+2*h>l+3*e → P h e r=0
def cleanA (P:Layers ℝ U) : Prop := ∀ h,P h 0=0
-- stronger mass for abr to account for second mark case.
lemma bare_abr (G:Matrix U U ℝ){P:ℕ→Gen ℝ U}(hz:P 0=0): cleanA (abr G P) := by
  intro h; funext r
  induction h using Nat.strong_induction_on generalizing r with
  | h n ih=>
    cases n with
    | zero=> rw [abr,hz]
    | succ n=>
      simp_rw [abr_next,Pi.smul_apply,Pi.add_apply]
      rw [ripple_zero_at _ _ _ (ih n n.lt_succ_self (r+2)),ravel_zero G (fun a b x y i j ha hb _=> Or.inl (show _ from by rw [show x=0 by omega]; exact ih a (by omega) _))]; simp
lemma span_abr (G:Matrix U U ℝ){P:ℕ→Gen ℝ U}(hh:shellK 2 P)(hz:P 0=0) : ∀ h e r,r>2+e ∨ r+2*h>3*e → abr G P h e r=0 := by
  intro h; induction h using Nat.strong_induction_on with
  | h n ih=>
    cases n with
    | zero=> intro e r H; rw [abr]; by_cases h:e=0
             · rw [h,hz]; rfl
             exact hh _ _ (by omega)
    | succ n=>
      intro e r H; simp_rw [abr_next,Pi.smul_apply,Pi.add_apply]
      rw [ripple_zero_at _ _ _ (ih n n.lt_succ_self e _ (by omega)),ravel_zero G ?z]; simp
      case z=>
        intro a b x y i j ha hb hc
        by_cases h:i+1>2+x ∨ i+1+2*a>3*x; exact Or.inl (ih a (by omega) _ _ h)
        exact Or.inr (ih b (by omega) _ _ (by omega))
lemma stops_abr (G:Matrix U U ℝ){P:ℕ→Gen ℝ U}(hh:shellK 2 P)(hz:P 0=0): stops 2 (abr G P):= fun h e r E=> span_abr G hh hz h e r (by omega)
lemma stops_bul (G:Matrix U U ℝ){D:Layers ℝ U}(d:∀ h e r,r>2+e ∨ r+2*h>3*e → D h e r=0){P:ℕ→Gen R U} (l:ℕ)(p:shellK l P) : stops l (bul G D P):= by
  intro h; induction h using Nat.strong_induction_on with
  | h n ih=>
    cases n with
    | zero=> intro e r H; rw [bul]; apply p; omega
    | succ n=> intro e r H; have he F : ravel F D (bul G D P) n e r=0 := ravel_zero F fun a b x y i j ha hb hc=> by
                  by_cases h:i+1>2+x ∨ i+1+2*a>3*x; exact Or.inl (d _ _ _ h)
                  exact Or.inr (ih b (by omega) _ _ (by omega))
               simp_rw [bul_next,Pi.smul_apply,Pi.add_apply,he,ripple_zero_at G _ r (ih n n.lt_succ_self e _ (by omega)),add_zero,smul_zero]

lemma order_parity (G:Matrix U U ℝ){P:ℕ→Gen ℝ U}(hp:∀ e r, e%2 ≠ r%2→P e r=0) : ∀ h e r,e%2 ≠ r%2→abr G P h e r=0 := by
  intro h; induction h using Nat.strong_induction_on with
  | h n ih=>
    cases n with
    | zero=> intro e r E; rw [abr]; exact hp _ _ E
    | succ n=>
      intro e r E; simp_rw [abr_next,Pi.smul_apply,Pi.add_apply]
      rw [ripple_zero_at _ _ _ (ih n n.lt_succ_self e _ (by omega)),ravel_zero G ?z]; simp
      case z=>
        intro a b x y i j ha hb hc
        by_cases h:x%2=(i+1)%2; exact Or.inr (ih b (by omega) _ _ (by omega))
        exact Or.inl (ih a (by omega) _ _ h)
end YM.WilsonCoeffUV.Blue
