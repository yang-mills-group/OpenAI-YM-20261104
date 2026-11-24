import YM.WilsonMS.Top.Acyclic
import YM.MS.Swirl.Sits
import YM.MS.Book.Ell

/-!
# Include the inserted fields in the BV computation

`tokM` is the finite-alphabet perturbative master equation in these symbols.
Verify cycles for numerator *as well as* denominator. The guard in this file
is bosonic parity, `Happy` means the constant has been removed before taking
the exponential. All steps once again in the actual MS input algebra.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS
open MS MS.Koszul MS.Cylinder MS.Book MS.Book.Convolve MS.Swirl
open MS.Orbit MS.Orbit.Cog MS.Puff MS.Puff.Engine MS.Puff.Actors MS.Puff.SplitP
open MS.Puff.Mom MS.Puff.Dynamics
open Finset

variable {A I : Type} [Fintype I] {p : Sector A} (B : Bonded p I) {S : Raw A ℂ}

abbrev liftedBV (S : Raw A ℂ) :=
  promote (quantumD B S)

abbrev bracketS :=
  pairW (tokenL (B.BV (R := ℂ)) true p)

variable {B} {X U V : T (Raw A ℂ)}

local notation "M" => PermV p

local infixl:70 " ⋆ " => Actors.core (PermV p)

lemma star_applyW (i : ℕ) : (X ⋆ V) i = ∑ j ∈ antidiagonal i, product p (X j.1) (V j.2) :=
  rfl

lemma bosonic_central (hv : U ∈ (M).guard) (V : T (Raw A ℂ)) : U ⋆ V = V ⋆ U := by
  ext1 n
  rw [star_applyW, star_applyW]
  apply Eq.trans _ (Finset.Nat.sum_antidiagonal_swap (f := fun i => product p (V i.1) (U i.2)))
  exact Finset.sum_congr rfl (fun i _ => Pure.central (hv i.1 (Set.mem_univ _)) (V i.2))

variable (hv : U ∈ (PermV p).guard) (hx : X ∈ (PermV p).guard)

variable (B)

lemma symBracketS (hv : V ∈ (M).guard) (hx : X ∈ (M).guard) : bracketS B V X = bracketS B X V := by
  ext1 n
  rw [bracketS, paired, paired]
  apply Eq.trans _ (Finset.Nat.sum_antidiagonal_swap (f := fun i => tokenL _ _ p (X i.1) (V i.2)))
  exact
    Finset.sum_congr rfl fun i _ =>
      link_commute (b := true) B.BV (hv _ (Set.mem_univ _)) (hx _ (Set.mem_univ _))

include hv hx in
lemma bracket_mul (V : T (Raw A ℂ)) :
    bracketS B (U ⋆ X) V = U ⋆ (bracketS B X V) + X ⋆ (bracketS B U V) := by
  have hh n (f : ℕ → ℕ → ℕ → Raw A ℂ) :
    (∑ i ∈ antidiagonal n, ∑ j ∈ antidiagonal i.1, f j.1 j.2 i.2) =
      ∑ i ∈ antidiagonal n, ∑ j ∈ antidiagonal i.2, f j.1 i.1 j.2 :=
    (associate _ n).symm.trans (Engine.rewrap SplitP.nat _ _ n)
  ext1 n
  simp_rw [Pi.add_apply, bracketS, paired, star_applyW, paired, map_sum, LinearMap.sum_apply]
  simp_rw [show
      ∀ i j k : ℕ,
        tokenL B.BV true p (product p (U i) (X j)) (V k) =
          product p (U i) (tokenL B.BV true p (X j) (V k)) +
            product p (X j) (tokenL B.BV true p (U i) (V k))
      from (fun i j k => (B.costs).paired_left (hx _ (Set.mem_univ _)) (hv _ (Set.mem_univ _))),
    Finset.sum_add_distrib]
  refine congr_arg₂ (· + ·) ?_ ?_
  · exact (associate (fun i j k => product p (U i) (tokenL _ _ p (X j) (V k))) n).symm
  exact hh n (fun i j k => product p (X j) (tokenL _ _ p (U i) (V k)))

lemma bracket_unit (X : T (Raw A ℂ)) : bracketS B (M).unit X = 0 := by
  have he := bracket_mul B (X := (M).unit) (U := (M).unit) (M).holds (M).holds X
  rw [(M).identityK, (M).identityK] at he
  exact (add_eq_left.mp he.symm)

variable {B}

lemma wages_mul (hv : U ∈ (M).guard) (V : T (Raw A ℂ)) (n : ℕ) :
    bracketS B ((M).wages U (n + 1)) V = (M).wages U n ⋆ (bracketS B U V) := by
  induction n with
  | zero =>
    rw [nextW, firstW, (M).identityR, (M).identityK]
    simp
  | succ n ih =>
    rw [nextW (n := n + 1), map_smul, LinearMap.smul_apply, bracket_mul _ hv (wage_earn hv _) _, ih, ←
      (M).star_a, nextNF n, map_smul, LinearMap.smul_apply, inv_smul_eq_iff₀ (zeroN' _)]
    push_cast
    module

variable [Fintype A] (h : Quadratic B S)
include h
local notation "BVstep" => liftedBV B S
local notation "ℛ" => ((2 : ℂ)⁻¹) • bracketS B U U

lemma lifted_mul (hv : U ∈ (M).guard) (V : T (Raw A ℂ)) :
    BVstep (U ⋆ V) = BVstep U ⋆ V + U ⋆ BVstep V + bracketS B U V := by
  ext1 n
  simp_rw [Pi.add_apply, bracketS, paired, liftedBV, promised, star_applyW, map_sum, ←
    Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ hJ
  have hx : Pure p false (U i) := hv i (Set.mem_univ _)
  simp_rw [promised, quantum_apply, h.classical_vector, h.promotesField.derives hx, cross_false',
    one_smul, link_even (b := true) B.BV hx (v := V j), map_add, LinearMap.add_apply]
  change _ = _ + link B.BV true p (U i) (V j)
  abel

lemma lifted_unit : BVstep (M).unit = 0 := by
  have he := lifted_mul (S := S) h (M).holds (M).unit
  rw [(M).identityK, (M).identityK, (M).identityR, bracket_unit, add_zero] at he
  exact add_eq_left.mp he.symm

include hv

lemma lifted_wages (n : ℕ) :
    BVstep ((M).wages U (n + 1 + 1)) = BVstep U ⋆ (M).wages U (n + 1) + ℛ ⋆ (M).wages U n := by
  let q := ℛ
  have hp (n : ℕ) (P : T (Raw A ℂ)) :
    U ⋆ (P ⋆ (M).wages U n) = (n + 1 : ℂ) • (P ⋆ (M).wages U (n + 1)) := by
    rw [← (M).star_a, bosonic_central hv, (M).star_a, nextNF n, map_smul]
  have hw (n : ℕ) : bracketS B U ((M).wages U (n + 1)) = (2 : ℂ) • (q ⋆ (M).wages U n) := by
    rw [symBracketS B hv (wage_earn hv (n + 1)), wages_mul (B := B) hv,
      bosonic_central (wage_earn hv n)]
    unfold q
    rw [map_smul, LinearMap.smul_apply, smul_inv_smul₀ (by norm_num : (2 : ℂ) ≠ 0)]
  induction n with
  | zero =>
    rw [nextW (n := 0 + 1), map_smul, lifted_mul h hv, hw]
    have hU : BVstep ((M).wages U 1) = BVstep U ⋆ (M).wages U 0 := by
      rw [nextW (n := 0), firstW, (M).identityR, (M).identityR]
      simp
    rw [hU, hp]
    dsimp only [q]
    rw [inv_smul_eq_iff₀ (zeroN' _)]
    norm_num
    module
  | succ n ih =>
    rw [nextW (n := n + 2), map_smul, lifted_mul h hv, hw, ih, map_add, hp, hp]
    dsimp only [q]
    rw [inv_smul_eq_iff₀ (zeroN' _)]
    push_cast
    module

lemma lifted_sum (n : ℕ) :
    BVstep ((M).cheers U (n + 2)) = BVstep U ⋆ (M).cheers U (n + 1) + ℛ ⋆ (M).cheers U n := by
  have he (i : ℕ) : (M).cheers U (i + 1) = (M).cheers U i + (M).wages U (i + 1) :=
    Finset.sum_range_succ ..
  induction n with
  | zero =>
    rw [he (0 + 1), map_add, lifted_wages hv h 0, he 0,
      (show (M).cheers U 0 = (M).wages U 0 from by simp [cheers]), nextW (n := 0), firstW, map_add,
      lifted_unit h, (M).identityR U]
    simp [(M).identityR, map_add]
    abel
  | succ n ih =>
    rw [he (n + 2), map_add, lifted_wages hv h (n + 1), ih, he (n + 1), he n]
    simp only [map_add]
    abel

omit h [Fintype A] in
lemma bracket_sum (B : Bonded p I) (V : T (Raw A ℂ)) (n : ℕ) :
    bracketS B ((M).cheers U (n + 1)) V = (M).cheers U n ⋆ bracketS B U V := by
  have he (i : ℕ) : (M).cheers U (i + 1) = (M).cheers U i + (M).wages U (i + 1) :=
    Finset.sum_range_succ ..
  induction n with
  | zero =>
    rw [he 0, map_add, LinearMap.add_apply, wages_mul (B := B) hv V,
      show (M).cheers U 0 = (M).wages U 0 from by simp [cheers], firstW, bracket_unit, zero_add]
  | succ n ih =>
    rw [he (n + 1), map_add, LinearMap.add_apply, wages_mul (B := B) hv V, ih, he n]
    simp only [map_add, LinearMap.add_apply]

variable (hz : U 0 = 0)
include hz
local notation "e" => exp0 p U

section replacement
omit [Fintype A] h hv
variable {E : Type} [AddCommGroup E] [Module ℂ E]

lemma diagonal (n i : ℕ) (hr : i ≤ n) : (M).cheers U n i = e i :=
  Actors.overbook (actor p) useN U hz hr

lemma limit_lift (P : Raw A ℂ →ₗ[ℂ] E →ₗ[ℂ] E) (V : T E) (n i : ℕ) (hr : i ≤ n) :
    pairW P ((M).cheers U n) V i = pairW P e V i := by
  rw [paired, paired]
  exact
    Finset.sum_congr rfl
      (fun j hj => by
        rw [diagonal hz n _
            (by
              obtain h := Finset.mem_antidiagonal.mp hj
              omega)])

lemma central_lift (V : T (Raw A ℂ)) (n i : ℕ) (hr : i ≤ n) : (V ⋆ (M).cheers U n) i = (V ⋆ e) i := by
  rw [star_applyW, star_applyW]
  exact
    Finset.sum_congr rfl
      (fun j hj => by
        rw [diagonal hz n _
            (by
              obtain h := Finset.mem_antidiagonal.mp hj
              omega)])

end replacement

lemma lifted_exp : BVstep e = (BVstep U + ℛ) ⋆ e := by
  ext1 i
  have he := congr_fun (lifted_sum hv h i) i
  unfold liftedBV at *
  rw [Pi.add_apply, promised, central_lift hz _ _ i (by omega), central_lift hz _ _ _ le_rfl,
    diagonal hz _ i (by omega)] at he
  rw [promised, he, map_add, LinearMap.add_apply, Pi.add_apply]

omit h [Fintype A] in
lemma bracket_exp (B : Bonded p I) (V : T (Raw A ℂ)) : bracketS B e V = e ⋆ bracketS B U V := by
  ext1 i
  change pairW _ _ _ _ = pairW (product (R := ℂ) p) _ _ _
  rw [← limit_lift hz (tokenL _ _ p) V (i + 1) i (by omega)]
  rw [← limit_lift hz (product p) (bracketS B U V) i i le_rfl]
  exact congr_fun (bracket_sum hv B V i) i

omit hz [Fintype A] in
lemma constant_part (ht : tokM B (useN.refineV S + U) = 0) : BVstep U + ℛ = 0 := by
  let Y := useN.refineV S
  let L := bracketS B
  have he (V : T (Raw A ℂ)) : L Y V = promote (classicalD B S) V := tile useN (tokenL _ _ p) S V
  have hh (P : Op A ℂ) (hx : P S = 0) : promote P Y = 0 := by
    ext1 i
    rw [promised]
    unfold Y refineV
    split
    exact hx
    exact map_zero _
  have hu : L Y Y = 0 := by
    rw [he]
    exact hh _ h.master
  change promote B.BV (Y + U) + (1 / 2 : ℂ) • L (Y + U) (Y + U) = 0 at ht
  rw [map_add, hh _ h.lap, zero_add] at ht
  simp only [map_add, LinearMap.add_apply, hu, zero_add] at ht
  rw [show L U Y = L Y U from symBracketS B hv (refineπ useN S (B := Center p) h.even), he] at ht
  have hp : BVstep U = promote (classicalD B S) U + promote B.BV U := rfl
  rw [hp]
  linear_combination (norm := module) ht

omit hz hv h [Fintype A] in
lemma observable (hr : modulo B (useN.refineV S + U) V = 0) : BVstep V + bracketS B U V = 0 := by
  unfold modulo at hr
  let P := tokenL (B.BV (R := ℂ)) true p
  simp only [LinearMap.add_apply, map_add] at hr
  have hh : pairW P (useN.refineV S) V = promote (classicalD B S) V := tile useN P S V
  have hp : BVstep V = promote (classicalD B S) V + promote B.BV V := rfl
  rw [hp]
  linear_combination (norm := abel) hr - hh

/-- The QME on the unmarked exponent and the Q-closed insertion imply
that every coefficient of the Wick numerator is a cycle. -/
lemma marked_cycles (ht : tokM B (useN.refineV S + U) = 0) (hr : modulo B (useN.refineV S + U) V = 0)
    (i : ℕ) : quantumD B S ((e ⋆ V) i) = 0 := by
  have H : BVstep (e ⋆ V) = 0 := by
    have hv' : e ∈ (M).guard := costCheer useN (actor p).holds (actor p).close hv
    rw [lifted_mul h hv' _, lifted_exp hv h hz, constant_part hv h ht,
      show (0 : T (Raw A ℂ)) ⋆ e = 0 from LinearMap.congr_fun (map_zero ((M).core)) _,
      show (0 : T (Raw A ℂ)) ⋆ V = 0 from LinearMap.congr_fun (map_zero ((M).core)) _, zero_add,
      bracket_exp hv hz B, ← map_add, observable hr, map_zero]
  exact congr_fun H i

lemma plain_cycles (ht : tokM B (useN.refineV S + U) = 0) (i : ℕ) : quantumD B S (e i) = 0 := by
  have H : BVstep e = 0 := by
    rw [lifted_exp hv h hz, constant_part hv h ht, map_zero, LinearMap.zero_apply]
  exact congr_fun H i

end YM.WilsonMS
