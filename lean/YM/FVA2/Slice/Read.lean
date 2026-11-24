import YM.FVA2.Wick.Ingredients
import YM.FVA2.Fourier.Bills
/-! # Real position-basis readings -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Slice
open Function Set Filter Finset Lattice
open MS MS.Plane MS.Cylinder Lab MS.Cylinder.Taylor MS.Book MS.Tone MS.City MS.Orbit
open MS.Koszul MS.Landau MS.Native MS.Native.Chart MS.Native.Wilsonian MS.Bare Focus
open Pert Orb Fourier
open Wick (Index bos bar sector eased Inks)
open scoped BigOperators Matrix Topology ContDiff InnerProductSpace
variable {G : Gauge} {n : Side} {A J : Type}
local notation "T" => Site n
local notation "L" => Transverse G n
local notation "Z" => SiteGhost G n
local notation "E" => FixedMode G n
local notation "C" => G.ColorIndex
local notation "Π₀" => panel G T
local notation "Γ" => glow G T

-- Include X-transverse even legs; YM.MS `reads` ignores every other leg.
lemma all_directions (v : Directions G n) : ∑ i:E, fieldDir G n v i • direction i = includeA G n v.1 := by
  -- directions only at Atom gauge; reorder
  let f (i : T) (a : Axis)(c:C) := projector ((i,a),c) (includeA G n v.1) • priv ((i,a),c)
  calc
    _ = ∑ a:Axis, ∑ c:C, ∑ i:T, f i a c := by
      have he (a : Axis)(z : Bool) (x:T)(c:C) : fieldDir G n v (((some a,z),c),x) • direction (((some a,z),c),x) = if z then 0 else f x a c := by
        cases z; · unfold f; rw [projector_k]; rfl
        exact smul_zero _
      have hv (z : Bool) (x:T)(c:C) : fieldDir G n v (((none,z),c),x) • direction (((none,z),c),x) = 0 := smul_zero _
      simp only [Fintype.sum_prod_type,Fintype.sum_bool,Fintype.sum_option,he,hv,Finset.sum_const_zero,
        if_true, Bool.false_eq_true, if_false, zero_add]
    _ = ∑ i:T, ∑ a:Axis, ∑ c:C, f i a c := by
      conv_lhs =>
        arg 2; intro i; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ = _ := by
      have h := Native.frame (includeA G n v.1)
      simp only [Fintype.sum_prod_type] at h; exact h

namespace Axes
variable (a : Axes G n A J) [Fintype J] [DecidableEq J]
local notation "b" => sector (A:=A) (J:=J)
local notation "I" => Index A J
local notation "X" => Inks (J:=J) a.X
local notation "δ" => Wick.pull a.P
local infixl:70 " ⋆ " => product b
local infixl:70 " ⋆₀ " => product (σbranch (G:=G) (n:=n))


lemma ease_basis (i : I) : (a.basis i).1 = eased a.X i := by
  rcases i with x|j|k
  · rw [show a.basis (.inl x)=_ from a.basis_b x]; rfl
  · rw [show a.basis (.inr (.inl j))=_ from a.basis_bar j]; rfl
  rw [show a.basis (.inr (.inr k))=_ from a.basis_c k]; rfl

/-- Tests on external legs preserving Taylor ranks exactly. -/
theorem read_pull {f : Chart.City G T→ℝ} (h : germ f) : δ (reads f) = X (f ∘ incCL G n) := by
  change δ (region.symm (reads f)).val = _
  rw [Wick.pull_shade]
  let W (i : I) (j : E) := fieldDir G n (a.basis i) j
  have ht (i:I) : (incCL G n ∘ eased a.X) i = ∑ j : E,W i j • direction j := by rw [all_directions (a.basis i), a.ease_basis]; rfl
  rw [Inks,Taylor.ink_ctrl_one]
  exact (Taylor.scale_pos direction _ W ht h).symm
  exact h

lemma calm {f : Chart.City G T → ℝ} (h : germ f) : germ (f ∘ incCL G n) := by
  let ht := (incCL G n).map_zero
  exact ((ht.symm ▸ h : ContDiffAt ℝ ω f (incCL G n 0)).comp (f:=incCL G n) 0
    (ContinuousLinearMap.contDiff (𝕜:=ℝ) («E»:=Transverse G n) (F:=Chart.City G T) (incCL G n)).contDiffAt)

variable [Fintype A]
lemma spin_ghost (x:T) (k:C) :
    δ (atLetter ((MS.Landau.ghost,k),x)) = ∑ i:J, (((a.c i).val x k):ℂ) • atLetter (Wick.ghost (A:=A) i) := by
  rw [Wick.letter_pull]; unfold Axes.P
  simp only [Fintype.sum_sum_type, placeMatrix, Matrix.of_apply,
    show ∀ i,a.basis (.inl i)=_ from fun i=> a.basis_b i,
    show ∀ i,a.basis (.inr (.inl i))=_ from fun i=> a.basis_bar i,
    show ∀ i,a.basis (.inr (.inr i))=_ from fun i=> a.basis_c i]
  simp [fieldDir, MS.Landau.ghost, place]
lemma spin_anti (p : Edge T) (k:C) :
    δ (atLetter ((anti p.2,k),p.1)) = ∑ i:J, (((gM (a.Y i)).val p k):ℂ) • atLetter (bar (A:=A) i) := by
  rw [Wick.letter_pull]; unfold Axes.P
  simp only [Fintype.sum_sum_type, placeMatrix, Matrix.of_apply,
    show ∀ i,a.basis (.inl i)=_ from fun i=> a.basis_b i,
    show ∀ i,a.basis (.inr (.inl i))=_ from fun i=> a.basis_bar i,
    show ∀ i,a.basis (.inr (.inr i))=_ from fun i=> a.basis_c i]
  simp [fieldDir, anti, place]
lemma spin_B (x:T) (k:C) : δ (atLetter ((gaugeC,k),x)) = 0 := by
  rw [Wick.letter_pull]; unfold Axes.P
  simp [placeMatrix, fieldDir, gaugeC, place]
end Axes
end YM.FVA2.Slice
