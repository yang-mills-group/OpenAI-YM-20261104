import YM.FVA2.Wick.Fermion
import YM.MS.Swirl.Sits
/-! # Some calculus in the MS `SpecB` algebra

`overlay` is exactly `Actors.core (PermV p)`. No factorial in the power series; the
factorials in the leg convention are handled independently. Keep notation local/scoped to FVA2.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Wick
open Function Set Finset
open MS MS.Koszul MS.Plane MS.Cylinder MS.Book Convolve MS.Orbit Cog MS.Swirl
open MS.Puff MS.Puff.Mom MS.Puff.Engine MS.Puff.Actors
open scoped BigOperators Topology ContDiff Matrix
variable {A B J : Type}

namespace Formal
abbrev Table (A : Type) := ℕ → Raw A ℂ
abbrev overlay (p : Sector A) := Actors.core (PermV p)
local notation "T" => Table A
variable {t v : Table A} {p : Sector A} {s : Sector B}
local infixl:70 " ⋆ " => product p
local infixl:70 " ★ " => overlay p

lemma coeff_prod (p : Sector A)(x y : T)(n : ℕ) : overlay p x y n = ∑ i∈Finset.antidiagonal n, product p (x i.1) (y i.2) := rfl
lemma coeff_zero (p:Sector A)(x y:T) : overlay p x y 0=product p (x 0) (y 0) := by simp only [coeff_prod,Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
lemma assoc (p:Sector A)(x y z:T) : overlay p (overlay p x y) z=overlay p x (overlay p y z) := (PermV p).star_a ..

abbrev band (p:Sector A) (b:Bool)(x:T) : Prop := ∀ i, Pure p b (x i)
lemma turns {u b:Bool}{x y : Table A} (h : band p u x)(g : band p b y) : x ★ y = (cross u b:ℂ) • (y ★ x) := by
  funext n; simp only [coeff_prod, Pi.smul_apply, Finset.smul_sum]
  rw [← Finset.Nat.sum_antidiagonal_swap (f:=fun i => x i.1 ⋆ y i.2)]; apply Finset.sum_congr rfl; intro _ _
  exact (h _).times_comm (g _)

abbrev even (p:Sector A) := allIndex (Center p) ℕ
lemma ev {x:Table A} : x∈even p ↔ band p false x := universe0 _
lemma central {x:Table A} (h:x∈even p)(y:T) : x ★ y=y ★ x := by
  funext n; rw [coeff_prod,coeff_prod,← Finset.Nat.sum_antidiagonal_swap (f:=fun i => x i.1 ⋆ y i.2)]; apply Finset.sum_congr rfl; intro _ _
  exact ((ev.mp h) _).central _
lemma even_add (x y : Table A) (h:x∈even p)(H:y∈even p) : x+y∈even p:= (even p).add_mem h H
lemma even_exp (h:t∈even p) : exp0 p t∈even p := Cinch.totalZ (P:=useN) (M:=actor p) h
lemma exp_zero (p:Sector A) {t:Table A} (h:t 0=0) : exp0 p t 0=coin 1 := Stencil.simple_E _ _ _ h -- ambiguous p uses type unif
lemma exp_add (h:t∈even p)(H:v∈even p)(hx:t 0=0)(hy:v 0=0) : exp0 p (t+v) = exp0 p t ★ exp0 p v := cheer_a h H hx hy
lemma time_comm {I J:Type}[AddCommGroup I][AddCommGroup J][Module ℂ I][Module ℂ J](L:I→ₗ[ℂ]J)(v:ℕ→I) : promote L (Swirl.clock useN I v) = Swirl.clock useN J (promote L v) := funext fun _=>map_smul L _ _
lemma time_exp (h:t∈ even p)(H:t 0=0) : Swirl.clock useN (Raw A ℂ) (exp0 p t) = Swirl.clock useN (Raw A ℂ) t ★ exp0 p t := (turn_clock useN (actor p)).idea h H
lemma time_weight (x:T)(n:ℕ) : Swirl.clock useN (Raw A ℂ) x n=(n:ℂ) • x n := rfl
lemma clock_prod (p : Sector A)(x y:T) : Swirl.clock useN (Raw A ℂ) (overlay p x y) = overlay p (Swirl.clock useN (Raw A ℂ) x) y +overlay p x (Swirl.clock useN (Raw A ℂ) y) := (turn_clock useN (actor p)).earns x y

-- indicators (s0 only)
def tab : Linear (Raw A ℂ) (Table A) where
  toFun := useN.refineV
  map_add' x y := by funext i; unfold SplitP.refineV; split <;> simp [*]
  map_smul' c y := by funext i; unfold SplitP.refineV; split <;> simp [*]

lemma tab_value (x : Raw A ℂ)(n:ℕ) : tab x n= if n=0 then x else 0 := by
  change useN.refineV x n=_; unfold SplitP.refineV; split <;> rename_i h
  · rw [if_pos (show n=0 from h)]
  rw [if_neg (show n≠0 from h)]
lemma tab_product (p:Sector A)(F : Raw A ℂ)(x : T)(k:ℕ) : overlay p (tab F) x k= product p F (x k) := congr_fun (useN.tile (product p) F x) k
lemma product_tab (p:Sector A)(F : Raw A ℂ)(x : T)(k:ℕ) : overlay p x (tab F) k= product p (x k) F := congr_fun (useN.tm (product p) F x) k
lemma tabs (p:Sector A)(F H : Raw A ℂ) : overlay p (tab F) (tab H)=tab (product p F H) := by
  funext i; rw [tab_product,tab_value,tab_value]; split_ifs <;> simp
lemma tab_left (x:T) : tab (coin (1:ℂ)) ★ x = x := (PermV p).identityK _
lemma tab_unit (p:Sector A) : (PermV p).unit=tab (coin 1) := rfl
lemma tab_band {x : Raw A ℂ}{b:Bool} (h:Pure p b x) : band p b (tab x) := fun i=>by rw [tab_value]; split; exact h; exact Pure.zero
lemma tab_good {x:Raw A ℂ}{S:Submodule ℂ (Raw A ℂ)}(h:x∈ S) : tab x∈ allIndex S ℕ:= refineπ useN x h
lemma promote_tab (L:Raw A ℂ→ₗ[ℂ] Raw B ℂ)(x : Raw A ℂ) : promote L (tab x) = tab (L x):= by
  funext i; rw [promised,tab_value,tab_value]; split; rfl; exact map_zero _

-- Γ package infinite-order with each row meaningful
abbrev OK (p:Sector A) := allIndex (FeeP p) ℕ
lemma overlay_ok (h:t∈OK p)(he:v∈OK p) : t ★ v ∈ OK p := ΤΓ_pair h he
lemma clock_ok (h:t∈OK p) : Swirl.clock useN (Raw A ℂ) t∈OK p:= fun i _=> (FeeP p).smul_mem (i:ℂ) (h i (Set.mem_univ _))
lemma exponent_ok (h:t∈OK p) : exp0 p t∈OK p := expΓ h

abbrev der (i:A) := promote (D (R:=ℂ) i)
lemma der_at (x:T)(i n): der i x n = D i (x n) := rfl
lemma der_product {b:Bool} (h:band p b t)(y:T)(i:A) : der i (t ★ y) = der i t ★ y + (cross (p i) b:ℂ) • (t ★ der i y) := by
  funext n; rw [der_at, Pi.add_apply, Pi.smul_apply]; simp_rw [coeff_prod,map_sum,
    D_product,show ∀ j,Koszul.sign p (p i) (t j)=_ from fun j => (h j).signs (p i),
    map_smul,LinearMap.smul_apply,der_at,Finset.sum_add_distrib, ← Finset.smul_sum]

lemma der_pow {x:Table A} (h:x∈even p) (n:ℕ) (j:A) :
    der j ((PermV p).power x (n+1))=(n+1:ℂ) • (der j x ★ (PermV p).power x n) := by
  induction n with
  | zero=>
    rw [power]; change der j (overlay p x (PermV p).unit)= _ • (overlay p (der j x) (PermV p).unit); unfold overlay; rw [(PermV p).identityR,(PermV p).identityR]; simp
  | succ n ih =>
    rw [power, der_product (ev.mp h), ih, cross_false', one_smul, map_smul]
    rw [← assoc p, central h, assoc, power]
    push_cast; module

/-- Differentiate the *formal* exponential of an even symbol with respect to a letter (of either
parity). This is not analytic differentiation of a series with assumed summability. -/
lemma der_exp (x : Table A)(h : x ∈ even p)(hz : x 0=0) (j : A) :
    der j (exp0 p x)= der j x ★ exp0 p x := by
  have hw (i:ℕ) : der j ((PermV p).cheers x (i+1))=der j x ★ (PermV p).cheers x i := by
    unfold Actors.cheers; rw [map_sum, Finset.sum_range_succ', Dynamics.firstW, tab_unit]; unfold der; rw [promote_tab, coin_nod,map_zero,add_zero, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold wages; rw [map_smul, show promote (D (R:=ℂ) j) ((PermV p).power x (n+1)) = _ from der_pow h n j,map_smul,smul_smul]
    rw [Dynamics.phase']; congr 1; field_simp
  have hh (i k : ℕ)(hk:i ≤ k) : exp0 p x i=(PermV p).cheers x k i := Eq.symm (overbook (actor p) useN x hz hk)
  funext n; rw [der_at, hh n (n+1) (by omega), ← der_at, hw,coeff_prod,coeff_prod]
  exact Finset.sum_congr rfl fun i hi => by rw [hh i.2 n (by obtain he:= Finset.mem_antidiagonal.mp hi; omega)]

lemma pull_exp [Fintype A] (L:Matrix A B ℂ)(he:Tie p s Lᵀ)(x:T) :
    promote (pull L) (exp0 p x) = exp0 s (promote (pull L) x) := by
  have h : Tether (pull L) (actor p) (actor s) := ⟨pull_coin L _,pull_product he⟩
  funext i; exact h.figure useN x i
end Formal
end YM.FVA2.Wick
