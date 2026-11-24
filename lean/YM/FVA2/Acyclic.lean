import YangMills.WilsonProof.NativeSupport.YM.MS.Book.Mask
import YM.MS.LoopIdentity

/-!
# Finite BV ingredient of the inversion-quotient Wilson computation

This works in the **same shuffle/derivative convention** as `YM.MS.Swirl`.
Rooting the site gauge algebra will make the single-letter flat complex acyclic.
Here's the algebra we use to pass to the master-closed integrands: the resulting
finite-polynomial complex (even with its rank-lowering Laplacian) has only constant
representatives modulo exact elements. Thus even two *different* Wick functionals
can be shown to give exactly the same coefficients by integration by parts. This
argument will not be applied to a complex containing unaccounted harmonic modes.
-/

set_option autoImplicit false

noncomputable section

namespace YM.FVA2

open Finset Matrix MS MS.Koszul MS.Book

namespace OddMatrix
variable {A : Type*} [Fintype A] {p : Sector A}

/-- `m i j` is the coefficient of slot `i` in Q applied to slot `j`. -/
abbrev Swaps (p : Sector A) (m : Matrix A A ℂ) : Prop :=
  ∀ i j, m i j ≠ 0 → p j = !p i

/-- Realize a matrix on *all* polynomial ranks; not just a linear-jet operation. -/
def lift (p : Sector A) (m : Matrix A A ℂ) (h : Swaps p m) : Shift ℂ p true where
  source i := Finset.univ.filter (fun j => by classical exact m i j ≠ 0)
  mat := m
  row i j hij := by
    have hj := h i j (Finset.mem_filter.mp hij).2
    simpa using hj

lemma hook_apply (m : Matrix A A ℂ) (h : Swaps p m) (i : A) (F : Raw A ℂ) :
    (lift p m h).hook i F = ∑ j, m i j • D j F := by
  classical
  simp only [Shift.hook, lift, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j hj hx
  simp only [Finset.mem_filter, hj, true_and, not_not] at hx
  simp only [hx, zero_smul]

variable {m r : Matrix A A ℂ} (h : Swaps p m) (k : Swaps p r) (F : Raw A ℂ)

omit [Fintype A] in
private lemma cross_vanish (m : Matrix A A ℂ) (h : Swaps p m)
    (q : A → Raw A ℂ) (i j : A) :
    m i j • ((cross true (p j) : ℂ) • q j) +
      (cross true (p i) : ℂ) • (m i j • q j) = 0 := by
  by_cases he : m i j = 0
  · simp [he]
  rw [h i j he]; cases p i <;> simp

lemma hook_graded (T : Shift ℂ p true) (i : A) :
    (lift p m h).hook i (T.Q F) +
      (cross true (p i) : ℂ) • T.Q ((lift p m h).hook i F) =
        ∑ j, m i j • T.hook j F := by
  simp_rw [hook_apply, T.deriving', map_sum, map_smul, Finset.smul_sum,
    smul_add, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by
    rw [add_assoc, cross_vanish m h (fun j => T.Q (D j F)), add_zero]

/-- Odd matrix applied twice differentiates each slot by the ordinary square.
The formula is on all lists (no shape- or compact-support restrictions). -/
lemma D_Q_sq (i : A) :
    D i ((lift p m h).Q ((lift p m h).Q F)) =
      (∑ j, (m*m) i j • D j F) + (lift p m h).Q ((lift p m h).Q (D i F)) := by
  let X := lift p m h
  have hx : X.hook i (X.Q F) + (cross true (p i) : ℂ) • X.Q (X.hook i F) =
      ∑ j, (m*m) i j • D j F := by
    rw [show _ = ∑ j, m i j • X.hook j F from hook_graded h F X i]
    simp_rw [X, hook_apply, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
  change D i (X.Q (X.Q F)) = _
  rw [X.deriving', X.deriving', map_add, map_smul, smul_add, ← add_assoc,
    hx, smul_smul, cross_cross, one_smul]

lemma Q_sq_zero (hm : m*m=0) : (lift p m h).Q ((lift p m h).Q F) = 0 := by
  funext l
  induction l generalizing F with
  | nil => exact Shift.nil ..
  | cons i l IH =>
    rw [D_eval i ((lift p m h).Q _), D_Q_sq]
    simp only [IH, hm, Matrix.zero_apply, zero_smul, Finset.sum_const_zero,
      zero_add]; rfl

lemma D_anti [DecidableEq A] (hr : r*m + m*r = 1)
    (i : A) :
    D i ((lift p m h).Q ((lift p r k).Q F) + (lift p r k).Q ((lift p m h).Q F)) =
      D i F + ((lift p m h).Q ((lift p r k).Q (D i F)) +
        (lift p r k).Q ((lift p m h).Q (D i F))) := by
  let X := lift p m h
  let Y := lift p r k
  let c : ℂ := cross true (p i)
  have hx := hook_graded h F Y i
  change X.hook i (Y.Q F) + c • Y.Q (X.hook i F) = _ at hx
  have hy := hook_graded k F X i
  change Y.hook i (X.Q F) + c • X.Q (Y.hook i F) = _ at hy
  have hs : c*c=1 := cross_cross ..
  have hu : (∑ j, m i j • Y.hook j F) + (∑ j, r i j • X.hook j F) = D i F := by
    simp_rw [X, Y, hook_apply, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm (f:=fun j a => (m i j*r j a) • D a F),
        Finset.sum_comm (f:=fun j a => (r i j*m j a) • D a F)]
    simp_rw [← Finset.sum_smul]; rw [← Finset.sum_add_distrib]
    simp_rw [← add_smul]
    have H (j : A) : (∑ k, m i k*r k j) + (∑ k, r i k*m k j) =
        if i=j then (1:ℂ) else 0 := by
      rw [← Matrix.mul_apply, ← Matrix.mul_apply, add_comm, ← Matrix.add_apply, hr]
      exact Matrix.one_apply
    simp [H, ite_smul]
  change D i (X.Q (Y.Q F) + Y.Q (X.Q F)) = _
  rw [map_add, X.deriving', Y.deriving', Y.deriving', X.deriving']
  simp only [map_add, map_smul, smul_add, smul_smul, cross_cross, one_smul]
  calc
    _ = (X.hook i (Y.Q F) + c • Y.Q (X.hook i F)) +
        (Y.hook i (X.Q F) + c • X.Q (Y.hook i F)) +
        (X.Q (Y.Q (D i F)) + Y.Q (X.Q (D i F))) := by dsimp only [c]; abel
    _ = _ := by rw [hx, hy, hu]

lemma euler_exact [DecidableEq A] (hr : r*m + m*r = 1) (l : List A) :
    (lift p m h).Q ((lift p r k).Q F) l + (lift p r k).Q ((lift p m h).Q F) l =
      (l.length : ℂ) * F l := by
  induction l generalizing F with
  | nil => simp
  | cons i l IH =>
    rw [← Pi.add_apply (M:=fun _ : List A=>ℂ)]
    rw [D_eval i (_+_), D_anti h k F hr, Pi.add_apply, Pi.add_apply, IH, at_D]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

lemma limit_shift {n : ℤ} (H : Limit F n) : Limit ((lift p m h).Q F) n := by
  intro l hl
  induction l generalizing F n with
  | nil => simp
  | cons i l IH =>
    have hn : n-1 < (l.length : ℤ) := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hl; omega
    rw [D_eval i ((lift p m h).Q _), Shift.deriving', hook_apply, Pi.add_apply]
    have hg (j : A) := H.tip j
    rw [Limit.sum _ (f:=fun j=>m i j • D j F) (fun j _ => (hg j).smul _) l hn]
    simp only [Pi.smul_apply, smul_eq_mul, zero_add, IH _ (hg i) hn, mul_zero]

lemma mask_shift (n : ℤ) : (lift p m h).Q (mask n F) = mask n ((lift p m h).Q F) := by
  funext l
  induction l generalizing F n with
  | nil =>
    by_cases hx : (([]:List A).length:ℤ) = n
    · rw [enough _ hx, Shift.nil, Shift.nil]
    rw [strange _ hx, Shift.nil]
  | cons i l IH =>
    rw [D_eval i ((lift p m h).Q _), D_eval i (mask n _), MS.Book.conn]
    rw [Shift.deriving', Shift.deriving']
    simp_rw [hook_apply, map_add, map_sum, map_smul, MS.Book.conn,
      Pi.add_apply, Pi.smul_apply, IH]

end OddMatrix

namespace RankDescent
variable {A : Type*} [Fintype A] [DecidableEq A] {p : Sector A}
  {m r : Matrix A A ℂ} {Δ : Op A ℂ} (h : OddMatrix.Swaps p m)
  (k : OddMatrix.Swaps p r)

include k
/-- Finite-polynomial `Δ + Q` cohomology supplier. -/
theorem constant_mod_exact {F : Raw A ℂ} {n : ℕ} (H : Limit F n)
    (hr : r*m+m*r=1) (Δrank : ∀ (u : Raw A ℂ) (l : ℤ), Limit u l → Limit (Δ u) (l-2))
    (Δsym : ∀ u : Raw A ℂ, Symm p u → Symm p (Δ u))
    (sq : ∀ u, Symm p u →
      (Δ + (OddMatrix.lift p m h).Q) ((Δ + (OddMatrix.lift p m h).Q) u) = 0)
    (hF : Symm p F) (hD : (Δ + (OddMatrix.lift p m h).Q) F=0) :
    ∃ (c : ℂ) (u : Raw A ℂ), Limit u n ∧ Symm p u ∧
      F = coin c + (Δ + (OddMatrix.lift p m h).Q) u := by
  let Q := OddMatrix.lift p m h
  let K := OddMatrix.lift p r k
  let δ := Δ + Q.Q
  induction n generalizing F with
  | zero =>
    refine ⟨F [],0,fun _ _ => rfl, Symm.zero, ?_⟩
    rw [map_zero, add_zero]
    funext l; cases l with
    | nil => rfl
    | cons i l => exact H _ (by simp)
  | succ n IH =>
    let t : ℤ := n+1
    let P := mask t F
    have hP : Limit P t := Limit.mod F t
    have hp : Symm p P := by
      intro l i j v
      by_cases he : ((l++i::j::v).length : ℤ)=t
      · have hv : ((l++j::i::v).length : ℤ)=t := by simpa using he
        unfold P; rw [enough _ he, enough _ hv]; exact hF ..
      have hv : ((l++j::i::v).length : ℤ)≠t := by simpa using he
      unfold P; rw [strange _ he, strange _ hv, mul_zero]
    push_cast at H
    change Limit F t at H
    have heQ : Q.Q P=0 := by
      change (OddMatrix.lift p m h).Q (mask t F)=_
      rw [OddMatrix.mask_shift]
      funext l
      by_cases he : (l.length:ℤ)=t
      · have hL := congr_fun hD l
        change Δ F l + Q.Q F l = 0 at hL
        rw [Δrank F t H l (by omega), zero_add] at hL
        exact (enough _ he).trans hL
      exact strange _ he
    let c : ℂ := (n:ℂ)+1
    have hc : c≠0 := by unfold c; exact_mod_cast (by omega : n+1≠0)
    let R := (c⁻¹) • K.Q P
    have hR : Symm p R := (K.sym hp).smul _
    have H' : Limit R t := (OddMatrix.limit_shift k _ hP).smul _
    have hx : Q.Q R=P := by
      funext l
      unfold R; rw [map_smul]
      change c⁻¹ * Q.Q (K.Q P) l= P l
      have hz := OddMatrix.euler_exact h k P hr l
      change Q.Q (K.Q P) l + K.Q (Q.Q P) l = _ at hz
      rw [heQ,map_zero,Pi.zero_apply,add_zero] at hz
      rw [hz]; by_cases he:(l.length:ℤ)=t
      · have el : l.length=n+1 := by unfold t at he; omega
        rw [el, show ((↑(n+1:ℕ) : ℂ))=c from Nat.cast_add_one ..]
        rw [← mul_assoc,inv_mul_cancel₀ hc,one_mul]
      rw [show P l = 0 from strange _ he, mul_zero, mul_zero]
    let G := F - δ R
    have hG : (Δ+Q.Q) G=0 := by
      change (Δ+Q.Q) (F - _)=_; rw [map_sub,hD, show (Δ+Q.Q) (δ R)=0 from sq R hR,sub_self]
    have hGs : Symm p G := hF.sub ((Δsym _ hR).add (Q.sym hR))
    have hGl : Limit G n := by
      intro l hl
      change F l - (Δ R l + Q.Q R l) = 0
      rw [hx, Δrank R t H' l (by unfold t; omega), zero_add]
      by_cases he:(l.length:ℤ)=t
      · rw [show P l = F l from enough l he,sub_self]
      rw [H l (by unfold t at *; omega), show P l = 0 from strange _ he,sub_self]
    obtain ⟨b,z,hzl,hzs,hz⟩ := IH hGl hGs hG
    refine ⟨b,z+R,?_,hzs.add hR,?_⟩
    · push_cast
      exact (hzl.up (by omega : (n:ℤ)≤n+1)).add H'
    change F - δ R = coin b + δ z at hz
    change F = coin b+δ _
    rw [map_add, ← add_assoc]; exact sub_eq_iff_eq_add.mp hz
end RankDescent

end YM.FVA2
