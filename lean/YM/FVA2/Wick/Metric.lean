import YM.FVA2.Wick.Ingredients
import YM.FVA2.Wick.Green

/-!
# Wick covariance in joint boson-odd real coordinates
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Wick
open Function Set Finset Lattice Matrix
open MS MS.Plane MS.Koszul MS.Cylinder Taylor MS.Orbit Cog MS.Swirl
open PertExtension.GaussianScore
open scoped BigOperators Topology ContDiff Matrix
variable {A J E : Type}

section bos
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (B : Law E) (e : Module.Basis A ℝ E) [Fintype A] [DecidableEq A]
local notation "P" => B.P

/-- The real Hessian inverse, complexified. -/
def bosonMatrix : Matrix A A ℂ := Matrix.of fun i j => B.wick (e.coord j) (e.coord i)
local notation "C" => bosonMatrix B e

def bosonHessian : Matrix A A ℂ := Matrix.of fun i j => P (e i) (e j)
lemma boson_ok : bosonHessian B e * C=1 := by
  ext i j
  rw [Matrix.one_apply]; let v := B.inverse (e.coord j)
  change ∑ k, (P (e i) (e k) : ℂ) * (e.coord k v:ℂ) = _
  calc
    _ = ∑ k, (P (e i) ( e.coord k v • e k) :ℂ) := Finset.sum_congr rfl fun k _=> by
      simp only [map_smul, smul_eq_mul, Complex.ofReal_mul]; exact mul_comm ..
    _ = (P (e i) v:ℂ) := by rw [← Complex.ofReal_sum, ← map_sum, show ∑ k, e.coord k v • e k=v from e.sum_repr _]
    _ = (e.coord j (e i):ℂ) := by rw [B.turns, B.applies]
    _ = _ := by simp [Finsupp.single_apply,apply_ite]
omit [Fintype A] [DecidableEq A] in
lemma wick_sym (i j : A) : C i j=C j i := by
  let K i := B.inverse (e.coord i)
  change ↑(e.coord i (K j)) = (↑(e.coord j (K i)) : ℂ)
  rw [show e.coord i=P (K i) from (B.applies _).symm,
      show e.coord j=P (K j) from (B.applies _).symm, B.turns]
end bos

section pair
local notation "b" => sector (A:=A) (J:=J)
local notation "L" => Index A J
variable [DecidableEq J]

def omega (J : Type) [DecidableEq J] : Matrix (J⊕J) (J⊕J) ℂ := Matrix.fromBlocks 0 1 (-1 : Matrix J J ℂ) 0
def antiBlock (A J : Type) [DecidableEq J] : Matrix (Index A J) (Index A J) ℂ :=
 Matrix.fromBlocks 0 0 0 (omega J)
def totalCov (Q : Matrix A A ℂ) (J : Type)[DecidableEq J] := Matrix.fromBlocks Q 0 0 (omega J)

lemma metric_square (x y : Matrix A A ℂ) [Fintype A] [Fintype J] [DecidableEq A] (h:x*y=1) :
  Matrix.fromBlocks (-x) 0 0 (omega J) * totalCov y J = -1 := by
  unfold totalCov omega
  rw [Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]
  simp only [Matrix.neg_mul, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    h, zero_add, add_zero]
  rw [← Matrix.fromBlocks_one,Matrix.fromBlocks_neg, ← Matrix.fromBlocks_one (l:=J) (m:=J), Matrix.fromBlocks_neg]; simp -- reverse rw ones hazard

lemma ghost_jet [Fintype J] (x y : L) : (∑ i:J, xy (A:=A) i i [x,y])=antiBlock A J x y:= by
  classical
  -- specialize Ψ rows; rank convention
  have he (i : J) : xy i i [x,y] = atLetter (bar i) [x] * atLetter (ghost i) [y] +
       cross (b x) (b y) * atLetter (bar i) [y] * atLetter (ghost i) [x] := by
    rw [D_eval x (xy _ _),xy,D_product]
    simp only [Pi.add_apply,D_eval y (product b _ _), D_product, nil_product]
    simp [atLetter,sign,degree_cons]; congr
  simp_rw [he]; rcases x with x|x|x <;> rcases y with y|y|y <;> simp [antiBlock,omega,Matrix.one_apply, atLetter,bar,ghost,sector,mul_ite,eq_comm]
  split_ifs <;> simp
end pair
-- analytical second derivative pack
section hess
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma ink_pair {f:E→ℝ} (hf:germ f)(e:A→E)(i j:A) : ink e f [i,j]= ((iteratedFDeriv ℝ 2 f 0 ![e j,e i]) : ℂ) := by
  have ht:= (hf.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)
  simp only [ink,layer,iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  unfold layer; rw [(ht.hasFDerivAt.clm_apply (u:=fun _=>e i) (hasFDerivAt_const (e i) 0)).fderiv]; simp -- args check
end hess
end YM.FVA2.Wick
