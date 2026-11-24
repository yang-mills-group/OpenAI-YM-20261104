import YM.FVA2.Slice.Body
import YM.FVA2.Wick.Metric

/-!
# Wick covariance comparison with the MS finite input.

`Master` is the image of the physical Landau covariance in Fourier coordinates. Precise estimates on
regulator removal are elsewhere. This type of identity is at fixed cutoff. OEdge interpretation assumes Even.
Includes the physical fermion orientation, root/mode exception. All rank cost arguments to
`View` remain finite; we do not assert equality on unlimited-rank power sequences.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Slice.Axes
open Function Set Filter Finset Lattice
open MS MS.Plane MS.Cylinder Lab MS.Cylinder.Taylor MS.Book MS.Tone MS.City MS.Orbit
open MS.Koszul MS.Landau MS.Native MS.Native.Chart MS.Native.Wilsonian
open MS.Orbit.Cog MS.Swirl MS.Swirl.Near
open Pert Orb Fourier
open Wick (Index bos bar sector eased Inks xy bosonMatrix totalCov)
open scoped BigOperators Matrix Topology ContDiff InnerProductSpace
variable {G : Gauge} {n : Side} {A J : Type}
variable (a : Axes G n A J) [Fintype A] [Fintype J] [DecidableEq J]
local notation "T" => Site n
local notation "L" => Transverse G n
local notation "b" => sector (A:=A) (J:=J)
local notation "I" => Index A J
local notation "X" => Inks (J:=J) a.X
local notation "B" => bosonMatrix (gaussian G n) a.X
local notation "S" => Fourier.kernel G n true
local notation "K" => Master G n true
local infixl:70 " ⋆ " => product b
local notation "F" => (pay true • flatH G n)

lemma body_zero : Wick.pull a.R F = -mask 2 (X (Slice.W G n)) + ∑ i:J, xy i i := by
  have he := a.weight_level 0
  change Wick.pull a.R (SendB G n true (Wilsonian.core G 0)) = _
  rw [he, Nat.cast_zero,zero_add]
  have hc : mask 0 (X (Slice.haar G n))=0 := by
    rw [Wick.mask_zero, show X (Slice.haar G n) [] = 0 from (by
       change (↑(Slice.haar G n 0) : ℂ)=0; rw [haar_zero, Complex.ofReal_zero])]
    funext l; cases l <;> rfl
  rw [hc,add_zero]; congr 1; apply Finset.sum_congr rfl; intro i _
  have h (j:J) : mask 0 (X (fun v=> a.M v i j)) = coin ((a.M 0 i j:ℝ):ℂ) := Wick.mask_zero _
  simp_rw [h, a.flat_M]
  rw [Finset.sum_eq_single i, Matrix.one_apply_eq, Complex.ofReal_one, ← (coin_pure (1:ℂ)).central]
  · rw [coin_product, one_smul]
  · intro j _ hj
    rw [Matrix.one_apply, if_neg (Ne.symm hj), Complex.ofReal_zero,← (coin_pure _).central, coin_product]; simp
  exact fun hi=> (hi (Finset.mem_univ _)).elim

lemma quad_read :
    a.Rᵀ * Matrix.of (fun i j => pay true * flatH G n [i,j]) * a.R = Matrix.fromBlocks
      ( -Wick.bosonHessian (gaussian G n) a.X ) 0 0 (Wick.omega J) := by
  ext i j
  rw [show (fun i j : FixedMode G n=> pay true * flatH G n [i,j])= fun i j=> F [i,j] from rfl,
     ← Wick.matrix_pair _ a.R, body_zero, Pi.add_apply, Pi.neg_apply,enough (h:=2) [i,j] rfl, Finset.sum_apply,
     Wick.ghost_jet,Inks,Wick.ink_pair (W_smooth G n),(W_origin G n).2.2]
  rcases i with i|i|i <;> rcases j with j|j|j
  all_goals simp [eased, Wick.bosonHessian, Wick.antiBlock, gaussian];
  exact Slice.sym_P (a.X j) (a.X i)

/-- Master in the transverse and ghost bases, including the factor two covariance from the half counts and
 both images. -/
theorem Wick_cov : S = a.R * totalCov B J * a.Rᵀ := by
  classical
  refine Wick.factor_matrix a.R S (Matrix.of fun i j => pay true * flatH G n [i,j])
    σbranch (kernel_symm _) (kernel_clear _) kernel_chc (basis_matrix_inj _) (basis_range _) _ ?_
  rw [a.quad_read]; exact Wick.metric_square _ _ (Wick.boson_ok ..) -- arguments order

theorem grain_eq : Matrix.of K = a.R * ((1/2:ℂ) • totalCov B J) * a.Rᵀ := by
  rw [Matrix.mul_smul, Matrix.smul_mul,← a.Wick_cov]; ext i j
  change K i j = (1/2:ℂ) * (2 * K i j); ring

/-- Operational pull on *every* finite degree cap. -/
theorem wick_ms (Q : Raw (FixedMode G n) ℂ) (h : Q ∈ Mini _) :
    View K Q = View ( ( (1/2:ℂ) • totalCov B J ): Matrix I I ℂ ) (Wick.pull a.R Q) := by
  rw [Wick.pull_Wick a.R _ Q h, ← a.grain_eq]; rfl
end YM.FVA2.Slice.Axes
