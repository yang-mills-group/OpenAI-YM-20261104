import YM.FormalBulk08.Wick.Bake

/-! Verify recursion reproduces actual Wick pairing on V and equivariance for
linear pullbacks. No comparison with analytic integration here. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Wick
open Series
open scoped Classical BigOperators
variable {R S : Type*} {V U : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]
variable [Fintype V] [Fintype U] (q : V → V → R)

open Polynomial
lemma wick_X_equ (s : ∀ i j,q i j=q j i) (p : Glyphs R V) (i : V) : bake q (MvPolynomial.X i*p) = C (MvPolynomial.X i) * bake q p + X * ∑ j, C (MvPolynomial.C (q i j)) * bake q (MvPolynomial.pderiv j p) := by
  have he j : grain j (bake q p) = bake q (MvPolynomial.pderiv j p) := by
    ext1 n; rw [grain_coeff,bake_coeff,bake_coeff, Derivation.map_smul]; congr 1
    induction n with
    | zero=> rfl
    | succ n ih=> rw [pow_succ',Module.End.mul_apply,Module.End.mul_apply,←press_commutes,ih]
  let a:= ∑ j,C (MvPolynomial.C (q i j)) * bake q (MvPolynomial.pderiv j p)
  refine bake_unique q _ _ ?_ (bake_law ..) ?_
  · simp
  change derivative (_ + X*a)=stove q (_ + X*a)
  have ha : derivative a=stove q a := by
     ext1 n; simp [a,bake_law, stove_coeff, finsetSum_coeff, MvPolynomial.C_mul']
  rw [_root_.map_add,derivative_mul,derivative_mul,derivative_C,derivative_X,zero_mul,zero_add,one_mul,bake_law,ha,_root_.map_add]; ext1 n
  have hz (n) : coeff (X * stove q a) n= coeff (stove q (X*a)) n := by
     cases n <;> simp [stove_coeff]
  simp only [coeff_add, hz, stove_coeff q (C _ * _), coeff_C_mul, press_mul_X q s];
  simp [a, add_assoc,← he, grain_coeff, stove_coeff,finsetSum_coeff]

lemma bake_unchanged (p : Glyphs R V) (h : press q p=0) : bake q p=C p := by
   refine bake_unique q _ _ ?_ (bake_law q p) ?_
   · simp
   ext1 n; cases n <;> simp [stove_coeff,h]
@[simp] lemma bake_one : bake q 1=1 := by rw [bake_unchanged q _ (press_inert _ _ (by simp)),_root_.map_one]
@[simp] lemma bake_C (a : R) : bake q (MvPolynomial.C a)=C (MvPolynomial.C a) := bake_unchanged q _ (press_inert _ _ (by simp))

/-- Heat at covariance Q, with symbolic mean left unfilled. -/
def hearth : Glyphs R V →ₗ[R] Glyphs R V := ((Polynomial.aeval (R:=Glyphs R V) (1 : Glyphs R V)).toLinearMap.restrictScalars R).comp (bake q)
lemma hearth_def (p : Glyphs R V) : hearth q p=(bake q p).eval 1 := by simp [hearth]
lemma hearth_X (s : ∀ i j,q i j=q j i) (p : Glyphs R V) (i : V) : hearth q (MvPolynomial.X i*p)= MvPolynomial.X i * hearth q p + ∑ j, (MvPolynomial.C (q i j)) * hearth q (MvPolynomial.pderiv j p) := by simp [hearth, wick_X_equ q s, eval_finsetSum]
@[simp] lemma hearth_C (a : R) : hearth q (MvPolynomial.C a)=MvPolynomial.C a := by simp [hearth_def]
@[simp] lemma hearth_one : hearth q 1=1 := by simp [hearth_def]

def moment : Glyphs R V →ₗ[R] R := (MvPolynomial.aeval (R:=R) (0 : V → R)).toLinearMap.comp (hearth q)
lemma moment_eq (p : Glyphs R V) : moment q p=MvPolynomial.aeval (R:=R) (0 : V → R) (hearth q p) := rfl
@[simp] lemma moment_C (a : R) : moment q (MvPolynomial.C a)= a := by simp [moment_eq]
@[simp] lemma moment_one : moment q 1=1 := by simp [moment_eq]
lemma paired (s : ∀ i j, q i j=q j i) (p : Glyphs R V) (i : V) : moment q (MvPolynomial.X i * p)= ∑ j, q i j * moment q (MvPolynomial.pderiv j p) := by simp [moment_eq,hearth_X q s]

open MvPolynomial hiding C X map eval
lemma moment_unique (s : ∀ i j,q i j=q j i) (A : Glyphs R V →ₗ[R] R) (ha : A 1=1)
    (hp : ∀ p i, A (MvPolynomial.X i * p) = ∑ j, q i j * A (MvPolynomial.pderiv j p)) : A = moment q := by
   apply LinearMap.ext; intro p
   suffices h : ∀ k : ℕ, ∀ x : Glyphs R V, x.totalDegree ≤ k → A x=moment q x from h _ _ (le_refl _)
   clear p; intro k; induction k using Nat.strong_induction_on with
   | _ k ih=>
     intro x hx
     conv_lhs => rw [x.as_sum]
     conv_rhs => rw [x.as_sum]
     simp_rw [_root_.map_sum]; apply Finset.sum_congr rfl; intro m hm
     by_cases hmm : m=0
     · subst m;change A (MvPolynomial.C _) = moment q (MvPolynomial.C _)
       rw [show ∀ r:R,MvPolynomial.C r=(r • (1 : Glyphs R V)) from fun r=>by rw [MvPolynomial.smul_eq_C_mul,mul_one]]
       simp [ha]
     obtain ⟨i,hi⟩ := Function.ne_iff.mp (show ⇑m ≠ (0 : V → ℕ) from fun he=> hmm (DFunLike.ext _ _ (congr_fun he)))
     · let b:=m-Finsupp.single i 1
       have hh : Finsupp.single i 1+b=m := add_tsub_cancel_of_le ?_
       · have hA:= (le_totalDegree hm).trans hx
         nth_rw 1 [←hh] at hA; rw [Finsupp.sum_add_index' (fun _=>rfl) (fun _ _ _=>rfl)] at hA; simp at hA
         let P:=MvPolynomial.monomial b (MvPolynomial.coeff m x)
         have hz : P.totalDegree<k := lt_of_le_of_lt (totalDegree_monomial_le ..) (by exact lt_of_lt_of_le (Nat.lt_add_of_pos_left (by omega)) hA)
         have he : (MvPolynomial.monomial m (MvPolynomial.coeff m x))=MvPolynomial.X i*P := by nth_rw 1 [← hh]; rw [monomial_single_add,pow_one]
         rw [he,hp,paired q s];exact Finset.sum_congr rfl fun j _=> by rw [ih _ hz _ ((pderiv_degree j P).trans (Nat.sub_le ..))]
       intro j; by_cases hj:j=i
       · subst j; rw [Finsupp.single_eq_same]; exact Nat.pos_of_ne_zero hi
       simp [hj]
end YM.FormalBulk08.Wick
