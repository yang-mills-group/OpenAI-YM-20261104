import YM.FVA2.Slice.Interaction
/-! # Rank accounting when dropping the zeroth interaction from NRG -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Wick
open Function Set Finset
open MS MS.Koszul MS.Cylinder Taylor MS.Plane MS.Book MS.Orbit
variable {A : Type} (p : Sector A) {x : Raw A ℂ}
lemma mask_rank_left {v : ℤ} (h : Book.rank v x) (n : ℤ) (y : Raw A ℂ) :
    mask (n+v) (product p x y) = product p x (mask n y) := by
  funext l
  by_cases hl : (l.length:ℤ)=n+v
  · rw [enough l hl, scattered,scattered]; apply scatter_congr; intro a b ha
    by_cases hx:(a.length:ℤ)=v; · rw [enough _ (by obtain hh:=split_length ha; omega)]
    rw [h a (by rw [mod_int]; exact hx), zero_mul, zero_mul]
  rw [strange l hl, (h.product (p:=p) (rankMod y n)) l (by rw [mod_int,add_comm v]; exact hl)]
lemma mask_zero (y : Raw A ℂ) : mask 0 y = coin (y []) := by
  funext l; cases l; exact enough [] rfl; exact strange _ (by simp; omega)
end Wick

namespace Slice.Axes
open Function Set Filter Finset Lattice
open MS MS.Plane MS.Cylinder Lab MS.Cylinder.Taylor MS.Book MS.Tone MS.City MS.Orbit
open MS.Koszul MS.Landau MS.Native MS.Native.Chart MS.Native.Wilsonian MS.Bare Focus
open MS.Swirl.Near
open Pert Orb Fourier
open Wick (pull Index bos bar sector eased Inks xy)
open scoped BigOperators Matrix Topology ContDiff InnerProductSpace
variable {G : Gauge} {n : Side} {A J : Type}
variable (a : Axes G n A J) [Fintype A] [Fintype J] [DecidableEq J]
local notation "T" => Site n
local notation "L" => Transverse G n
local notation "b" => sector (A:=A) (J:=J)
local notation "I" => Index A J
local notation "X" => Inks (J:=J) a.X
local infixl:70 " ⋆ " => product b

omit [Fintype A] in
lemma send_pulled (F : Dot G Cover) : Wick.pull a.R (SendB G n true F) = Wick.pull a.P (Cog.pay true • docket n F) := by
  rw [send_cover, Wick.pull_comp, basis_unpack a.basis]
omit [Fintype A] in
lemma mark_pulled (F : Dot G Cover) (x c : Cover) :
    Wick.pull a.R (Mark_T G n x c F) = Wick.pull a.P (enters n (Lab.Shift (x+c) F)) := by
  rw [mark_cover, Wick.pull_comp, basis_unpack a.basis]

/-- The rank legs including the free quadratic part (order zero). This for the team before
reparametrizing its coupling (i.e. on `Wilsonian.core`). -/
theorem weight_level (k : ℕ) :
    Wick.pull a.R (SendB G n true (Wilsonian.core G k)) =
      -mask ((k:ℤ)+2) (X (Slice.W G n)) + mask k (X (haar G n)) +
        ∑ i:J, ∑ j:J, xy i j ⋆ mask k (X (fun v => a.M v i j)) := by
  have hm (v : ℤ) (F : Dot G Cover) : Wick.pull a.R (SendB G n true (levels v F k)) =
      mask ((k:ℤ)+v) (Wick.pull a.P (Cog.pay true • docket n F)) := by
    rw [a.send_pulled]; have he : docket n (levels v F k) = mask ((k:ℤ)+v) (docket n F) :=
      congr_fun (level_up v F n true) k
    rw [map_smul, he, Wick.pull_mask, map_smul, map_smul]
  rw [Wilsonian.core, Pi.add_apply,map_add,map_add, hm, hm, Haar_contact, Wilson_contact]
  simp_rw [map_add,map_sum, map_neg, add_zero (k:ℤ), Wick.mask_rank_left b (Wick.xy_deg _ _)]
  abel
end YM.FVA2.Slice.Axes
