import YM.FVAAlt2.Pull
import YM.MS.Tone.Pitch
import YM.CellFourier.Mesh

/-!
# Exact based Fourier map on a Wilson lattice cylinder

We use based modes (not shifted by half-edges); thus no midpoint multipliers
at the Brillouin-zone boundary in a frequency loop. This is still *torus*
Fourier. The b=true quotient is implemented in the covariance, not by
changing the Fourier table here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2
open Finset MS MS.Koszul MS.Book MS.Cylinder MS.Plane MS.Native MS.Cylinder.Lab
open MS.Tone MS.Landau Lattice

abbrev Mode (G : Gauge) (n : Side) := LightMode G (Site n)

def fourier (G : Gauge) (n : Side) : Matrix (Mode G n) (Mode G n) ℂ := fun p x =>
  way id p.1 x.1 * Bloch.cell p.2 x.2

local notation "BranchM" => Branch
variable {G : Gauge} {n : Side}
local notation "B" => BranchM G Axis
local notation "F" => fourier G n

lemma fourier_on (b:B) (p x:Site n) : F (b,p) (b,x) = Bloch.cell p x := by
  unfold fourier; rw [show way id b b=(1:ℂ) from only id b]; exact one_mul _
lemma fourier_off {b b':B} (h:b≠b') (p x:Site n) : F (b,p) (b',x) = 0 := by
  unfold fourier; rw [need id h,zero_mul]

lemma fourier_Tie (n:Side) (G:Gauge) : Tie Draft.DotFlip Draft.DotFlip (fourier G n) := by
  rintro ⟨i,x⟩ ⟨j,p⟩ ht
  have h : i=j := Classical.byContradiction fun he => ht (fourier_off (Ne.symm he) ..)
  subst j; rfl

def backwards (G:Gauge) (n:Side) : Matrix (Mode G n) (Mode G n) ℂ :=
  (((n.val:ℂ)^4)⁻¹) • (fourier G n).conjTranspose

lemma fourier_back (n:Side) (G:Gauge) : fourier G n * backwards G n = 1 := by
  ext ⟨b,p⟩ ⟨d,q⟩
  simp only [backwards, Matrix.mul_apply, Fintype.sum_prod_type (α₁:=Branch G Axis) (α₂:=Site n), Matrix.smul_apply,
    Matrix.conjTranspose_apply, smul_eq_mul, Matrix.one_apply]
  rw [Finset.sum_eq_single b]
  · simp_rw [fourier_on]
    by_cases h : d=b
    · subst d
      simp only [fourier_on, Complex.star_def, Bloch.cell_bar, Prod.mk.injEq, true_and]
      simp_rw [show ∀ (x : Site n), Bloch.cell p x * _ = _ from
        fun x => mul_left_comm (Bloch.cell p x) (((n.val:ℂ)^4)⁻¹) ((Bloch.cell q x)⁻¹),
        ← Finset.mul_sum]
      rw [Bloch.orthogonal]
      split
      · exact inv_mul_cancel₀ (pow_ne_zero _ (Bloch.side_ne _))
      exact mul_zero _
    rw [if_neg (by simp [Ne.symm h])]; simp [fourier_off h]
  · intro y _ h; simp only [fourier_off h.symm, zero_mul, Finset.sum_const_zero]
  simp

lemma backwards_fourier (n:Side) (G:Gauge) : backwards G n * fourier G n = 1 :=
  mul_eq_one_comm.mpr (fourier_back n G)

/-- The character factor is the same at *every* leg. Preserve this also on
mixed odd/even legs. -/
lemma shift_character (u : Dot G (Site n)) (z : Site n) (w : List (Mode G n)) :
    pull F (Lab.Shift z u).val w = Bloch.cell (net w) z * pull F u.val w := by
  rw [← eq_pull, ← eq_pull]
  unfold Lab.Shift transport; rw [study]
  let L (p x:Mode G n) := F p (post (fun i => z+i) x)
  have hl (p x : Mode G n) : L p x = Bloch.cell p.2 z * F p x := by
    unfold L fourier post; rw [Bloch.cell_add]; ring
  change shade L u w = _
  induction w generalizing u with
  | nil=> simp [Bloch.cell, net]
  | cons i w ih=>
    obtain ⟨s,hs⟩ := fromCyl u
    rw [deriv_lum L i u hs, deriv_lum F i u hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _=> ?_
    rw [hl, ih (enter x u), net_cons, Bloch.cell_duality (_+_), Bloch.cell_add,
      Bloch.cell_duality z, Bloch.cell_duality z (net w)]; ring

lemma sumHome_pull (u : Dot G (Site n)) (w : List (Mode G n)) :
    pull F (Lab.sumHome u).val w =
      if net w=0 then (n.val:ℂ)^4 * pull F u.val w else 0 := by
  rw [show pull F (Lab.sumHome u).val w = ∑ x : Site n, pull F (Lab.Shift x u).val w by
        rw [← eq_pull,total_uses,map_sum,Finset.sum_apply]; simp_rw [eq_pull]]
  simp_rw [shift_character, ← Finset.sum_mul]; split
  next he => rw [he]; simp [Bloch.cell]
  next he => rw [Bloch.sum_cell he,zero_mul]

end YM.FVAAlt2
