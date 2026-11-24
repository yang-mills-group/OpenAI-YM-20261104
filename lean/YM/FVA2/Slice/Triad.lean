import YM.FVA2.Slice.Density
import YM.FVA2.Slice.Complex

/-! # A coordinate system for the finite real Landau slice and its ghosts

The column basis c is **minus** dual to the (arbitrary) antighost basis for the Laplace metric,
so the M0 used in this coordinate system is `I`. This doesn't change the `det(A)/det(A0)`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Wick
open MS MS.Koszul MS.Cylinder
/-- Indices for a boson basis, then the antighost and ghost bases. -/
abbrev Index (A J : Type) := A ⊕ (J ⊕ J)
variable {A J : Type}
abbrev bos (a : A) : Index A J := .inl a
abbrev bar (j : J) : Index A J := .inr (.inl j)
abbrev ghost (j : J) : Index A J := .inr (.inr j)
abbrev sector : Sector (Index A J) := Sum.elim (fun _ => false) (fun _=> true)
end Wick

namespace Slice
open Function Set Filter Finset Lattice MeasureTheory
open MS MS.Koszul MS.Cylinder MS.Cylinder.Taylor MS.City MS.Orbit MS.Tone MS.Landau
open MS.Native MS.Native.Chart MS.Bare
open Pert Orb PertExtension.GaussianScore Fourier
open Wick (Index bos bar sector)
open scoped BigOperators Matrix Topology ContDiff InnerProductSpace
variable {G : Gauge} {n : Side}
local notation "T" => Site n
local notation "L" => Transverse G n
local notation "Z" => SiteGhost G n

lemma lap_neg (v : Z) (h:v≠0) : pair (0:L) v v < 0 := by
  rw [pair_zero]; apply neg_lt_zero.mpr
  unfold linkPair
  apply half_pos
  have hh : ∃ i : Edge T, (gM v).val i ≠ 0 := by
    by_contra! he
    exact h (gM_injective (by rw [map_zero]; exact Subtype.ext (funext he)))
  obtain ⟨i,hi⟩ := hh
  exact Finset.sum_pos' (fun j _ => real_inner_self_nonneg) ⟨i, Finset.mem_univ _, lt_of_le_of_ne real_inner_self_nonneg (fun he => hi (inner_self_eq_zero.mp he.symm))⟩

/-- Row transpose of the free ghost bilinear form. -/
def ghostDual (G : Gauge) (n : Side) : SiteGhost G n ≃ₗ[ℝ] Module.Dual ℝ (SiteGhost G n) :=
  let P := LinearMap.mk₂ ℝ (fun i j : SiteGhost G n => pair (0:Transverse G n) j i)
    (fun x y z => by simp [pair_zero, linkPair, inner_add_right, Finset.sum_add_distrib]; ring)
    (fun c x z => by simp [pair_zero, linkPair, real_inner_smul_right, ← Finset.mul_sum]; ring)
    (fun x y z => by simp [pair_zero, linkPair, inner_add_left, Finset.sum_add_distrib]; ring)
    (fun c x y => by simp [pair_zero, linkPair, real_inner_smul_left, ← Finset.mul_sum]; ring)
  have inj : Injective P := LinearMap.ker_eq_bot.mp (bot_unique (by
    intro i hi; by_contra he
    exact (lap_neg i he).ne (LinearMap.congr_fun (LinearMap.mem_ker.mp hi) i)))
  LinearEquiv.ofBijective P ⟨inj,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp inj⟩

variable {A J : Type}
structure Axes (G : Gauge) (n : Side) (A J : Type) where
  X : Module.Basis A ℝ (Transverse G n)
  Y : Module.Basis J ℝ (SiteGhost G n)

namespace Axes
variable (a : Axes G n A J) [Fintype J] [DecidableEq J]
local notation "I" => Index A J

def c : Module.Basis J ℝ Z := a.Y.dualBasis.map (ghostDual G n).symm
def M (x : L) : Matrix J J ℝ := Matrix.of (fun i j => pair x (a.Y i) (a.c j))
lemma flat_pair (i j : J) : pair (0:L) (a.Y i) (a.c j) = if i=j then 1 else 0 := by
  change (ghostDual G n) (a.c j) (a.Y i) = _
  unfold c; rw [Module.Basis.map_apply, LinearEquiv.apply_symm_apply]
  simp [Finsupp.single_apply]
lemma flat_M : a.M 0=1 := by ext i j; exact (a.flat_pair i j).trans (Matrix.one_apply ..).symm
lemma germ_M (i j : J) : germ (fun x : L => a.M x i j) := pair_smooth ..

def basis : Module.Basis I ℝ (Directions G n) := a.X.prod (a.Y.prod a.c)
lemma basis_b (i : A) : a.basis (bos i)=(a.X i,0) := by rw [basis,Module.Basis.prod_apply]; rfl
lemma basis_bar (i : J) : a.basis (bar i)=(0,(a.Y i,0)) := by
  calc
    a.basis (bar i) = ((0:L),(a.Y.prod a.c) (Sum.inl i)) := by rw [basis,Module.Basis.prod_apply]; rfl
    _ = _ := by rw [Module.Basis.prod_apply]; rfl
lemma basis_c (i : J) : a.basis (Wick.ghost i)=(0,(0,a.c i)) := by
  calc
    a.basis (Wick.ghost i) = ((0:L),(a.Y.prod a.c) (Sum.inr i)) := by rw [basis,Module.Basis.prod_apply]; rfl
    _ = _ := by rw [Module.Basis.prod_apply]; rfl
abbrev P := placeMatrix a.basis
abbrev R := basisMatrix a.basis

lemma tie : Tie σbranch sector a.Pᵀ := by
  rintro ⟨⟨⟨_|i',b⟩,q⟩,p⟩ j
  all_goals cases b <;> rcases j with v|v|v
  all_goals (first | exact fun _=>rfl | skip)
  all_goals simp only [P, Matrix.transpose_apply, placeMatrix, Matrix.of_apply,
    show ∀ i,a.basis (.inl i)=_ from fun i=> a.basis_b i,
    show ∀ i,a.basis (.inr (.inl i))=_ from fun i=> a.basis_bar i,
    show ∀ i,a.basis (.inr (.inr i))=_ from fun i=> a.basis_c i]
  all_goals simp [fieldDir,place]
lemma tieR : Tie σbranch sector a.Rᵀ := Wick.tie_comp (toFreq G n) (pack_tie G n) a.P a.tie
end Axes
end Slice
end YM.FVA2
