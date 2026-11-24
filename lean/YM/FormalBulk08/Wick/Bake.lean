import YM.FormalBulk08.Wick.Press
import Mathlib.RingTheory.Derivation.MapCoeffs

/-!
Free Wick evolution time `s` polynomial coefficient ring. Separate from the coupling.
Triangle recursion in s with no inverses of quadratic interactions.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Wick
open Series Polynomial
open scoped BigOperators
variable {R : Type*} {V : Type*} [CommRing R]

/-- Time letters free for `press`. Polynomial derivation coefficientwise. -/
def grain (i : V) : Derivation R (Polynomial (Glyphs R V)) (Polynomial (Glyphs R V)) :=
   PolynomialModule.equivPolynomialSelf.compDer (MvPolynomial.pderiv i).mapCoeffs
@[simp] lemma grain_coeff (i:V) (p : Polynomial (Glyphs R V)) (n) : coeff (grain i p) n=MvPolynomial.pderiv i (coeff p n) := rfl

variable [Algebra ℚ R]
def ounce (R : Type*) [CommRing R] [Algebra ℚ R] (k : ℕ) := PowerSeries.coeff k (PowerSeries.exp R)
lemma ounce_succ (k) : ounce R (k+1)*((k+1:ℕ):R)=ounce R k := by
   have h:=congr_arg (PowerSeries.coeff k) (PowerSeries.derivative_exp R)
   rw [PowerSeries.coeff_derivative, ← Nat.cast_succ] at h; exact h
@[simp] lemma ounce_zero : ounce R 0=1 := by simp [ounce]
lemma ounce_map {S : Type*} [CommRing S] [Algebra ℚ S] (f : R →+* S) (k) : f (ounce R k)=ounce S k := by simp [ounce]

variable [Fintype V] (q : V→V→R)
def heatLetter (p : Glyphs R V) : Polynomial (Glyphs R V) :=
   ∑ k ∈ Finset.range (p.totalDegree+1), monomial k (ounce R k • (press q ^ k : Module.End R _) p)
lemma heat_letter (p : Glyphs R V) (k) : coeff (heatLetter q p) k= ounce R k • (press q ^ k : Module.End R _) p := by
   classical
   simp only [heatLetter, finsetSum_coeff, coeff_monomial]
   by_cases h : k ≤ p.totalDegree
   · rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr (by omega))]; all_goals simp_all
   rw [press_nilpotent q p k (by omega),smul_zero]
   exact Finset.sum_eq_zero fun i hi=> if_neg (Ne.intro (by have := Finset.mem_range.mp hi; omega)) -- name

def bake : Glyphs R V →ₗ[R] Polynomial (Glyphs R V) where
   toFun := heatLetter q
   map_add' := by intro _ _;ext1 i; simp [heat_letter,smul_add]
   map_smul' := by intro a p;ext1 i; simp only [heat_letter, map_smul, RingHom.id_apply, coeff_smul]; rw [smul_comm]
lemma bake_coeff (p : Glyphs R V) (k) : coeff (bake q p) k= ounce R k • (press q ^ k : Module.End R _) p := heat_letter ..
@[simp] lemma bake_initial (p : Glyphs R V) : coeff (bake q p) 0=p := by rw [bake_coeff]; simp

/-- Absolute covariance calculus includes zeros for external coordinates,
    so evaluation-at-zero on active links is a final, separate operation. -/
def stove : Polynomial (Glyphs R V) →ₗ[R] Polynomial (Glyphs R V) := ∑ i,∑ j, halve (q i j) • ((grain i).toLinearMap.comp (grain j).toLinearMap)
lemma stove_coeff (p : Polynomial (Glyphs R V)) (i) : coeff (stove q p) i = press q (coeff p i) := by simp [stove,press,finsetSum_coeff]
lemma stove_eq (p : Polynomial (Glyphs R V)) : stove q p=∑ i,∑ j,C (MvPolynomial.C (halve (q i j))) * grain i (grain j p) := by
   ext1 n; simp [stove_coeff,press_eq,finsetSum_coeff]

lemma bake_law (p : Glyphs R V) : derivative (bake q p)=stove q (bake q p) := by
   ext1 n; simp only [coeff_derivative,bake_coeff,stove_coeff, map_smul, ← Nat.cast_succ]
   rw [pow_succ', Module.End.mul_apply]
   -- nat cast multiplication on Glyphs to scalar, ounce recursion
   simp only [MvPolynomial.smul_eq_C_mul]
   rw [mul_right_comm,←_root_.map_natCast MvPolynomial.C,←_root_.map_mul,ounce_succ]

lemma bake_unique (p g : Polynomial (Glyphs R V)) (he : coeff p 0=coeff g 0) (hp : derivative p=stove q p) (hg : derivative g=stove q g) : p=g := by
   ext1 n; induction n with
   | zero=> exact he
   | succ n ih=>
     have h : coeff (derivative p) n=coeff (derivative g) n := by rw [hp,hg,stove_coeff,stove_coeff,ih]
     rw [coeff_derivative,coeff_derivative] at h
     refine IsUnit.mul_left_inj ?_ |>.mp h
     simpa only [_root_.map_natCast, Nat.cast_succ, _root_.map_one, _root_.map_add] using (((isUnit_iff_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero n)) : IsUnit (↑(Nat.succ n):ℚ)).map (algebraMap ℚ (Glyphs R V)))
end YM.FormalBulk08.Wick
