import YM.FVA2.Slice.Wick
import YM.FVA2.Wick.Ticket
import YM.FVA2.Wick.Integrate

/-!
# The real unmarked exponent exactly removes the MS input's free quadratic

Exact power series identities; before ratio normalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Slice
open Function Set Filter Finset Lattice
open MS MS.Cylinder Lab MS.Cylinder.Taylor MS.Book Convolve Program MS.Tone MS.City MS.Orbit
open MS.Koszul MS.Landau MS.Native MS.Native.Chart MS.Native.Wilsonian MS.Orbit.Cog MS.Swirl MS.Swirl.Near
open MS.Puff MS.Puff.Engine MS.Puff.Mom
open PertExtension.GaussianScore
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge MultiGauge.Splice
open Wick (Index bos bar sector eased Inks xy bosonMatrix totalCov)
open PowerSeries (coeff)
open Wick Gem Fermion Boson
open Formal (overlay)
open scoped BigOperators Matrix Topology ContDiff InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {A J : Type}

/-- MS input exponent prior to applying `Stripped t` coupling change. -/
def before (G : Gauge) (n:Side) (k:ℕ) := if k=0 then (0:Orbit.BL (FixedMode G n)) else SendB G n true (Wilsonian.core G k)
lemma nil_before : before G n 0=0 := if_pos rfl
lemma before_ok : before G n∈ Formal.OK σbranch := by
  intro i _; unfold before; split; exact (FeeP σbranch).zero_mem; exact Near.memBill (n:=i+2) (crisp _ _) (by obtain h := participates G i; exact_mod_cast h)

namespace Axes
variable [FA:Fintype A] [FJ:Fintype J] [DJ:DecidableEq J]
variable (a : Axes G n A J)
local notation "T" => Site n
local notation "L" => Transverse G n
local notation "b" => sector (A:=A) (J:=J)
local notation "I" => Index A J
local notation "F" => before G n
local notation "Q" => Fermion.exponent a.X a.M
local notation "Y" => Boson.bills (J:=J) a.X
local notation "δ" => Wick.pull a.R
local notation "U" => Permit (Transverse G n)
local notation "W" => Slice.W G n
local infixl:70 " ⋆ " => product b
local infixl:70 " ★ " => overlay b
local infixl:70 " ⋆₀ " => overlay (σbranch (G:=G) (n:=n))
local notation "Ω" => MultiGauge.Stack.rise
local notation "Υ" => MultiGauge.Stack.advancing W
local notation "Ξ" => MultiGauge.Stack.exponential Υ
local notation "Lφ" => Ω (Slice.haar G n)
local notation "S" => exp0 σbranch F


omit FA FJ DJ in
lemma real_first : Y Υ 0=0 ∧ Y Lφ 0=0 := by
  constructor
  · rw [at_bill,PowerSeries.coeff_zero_eq_constantCoeff_apply, MultiGauge.Stack.advancing_zero, map_zero]
  rw [analytic _ _ (haar_smooth G n), first,haar_zero]; funext l; cases l <;> rfl

lemma exponent_body : promote δ F = Y Υ+ Y Lφ + Q := by
  funext i
  rw [promised]
  by_cases hi:i=0
  · rw [hi,nil_before,map_zero,Pi.add_apply,Pi.add_apply,exp_first a.X _ a.flat_M,
          a.real_first.1,a.real_first.2,add_zero,add_zero]
  unfold before; rw [if_neg hi,a.weight_level]
  have hr : (Y Υ) i= -mask (i+2) (Inks a.X W) := by
    rw [MultiGauge.Stack.advancing,map_add,Pi.add_apply, Boson.tab_const, Formal.tab_value, if_neg hi,add_zero,
       Boson.at_bill, MultiGauge.Stack.drop,PowerSeries.coeff_mk,map_neg,map_neg, ← Boson.at_bill,
       Boson.analytic a.X _ (W_smooth _ _)]
    unfold Gem.letter Inks; rw [show (((2:ℕ)+i:ℕ):ℤ)=(i:ℤ)+2 from (by omega)]
  have hx (u v:J) : Gem.letter (eased (J:=J) a.X) (minus a.M u v) i=mask i (Inks a.X (fun x=> a.M x u v)):= by
    rw [minus_eq a.X a.M a.germ_M,Pi.sub_apply]; split
    next he => rw [Formal.tab_value,if_neg hi,sub_zero]; rfl
    next _ => rw [Pi.zero_apply, sub_zero]; rfl
  unfold Fermion.exponent
  simp_rw [Pi.add_apply, Finset.sum_apply, Formal.tab_product,hx]
  rw [hr, Boson.analytic a.X _ (haar_smooth _ _ )]; rfl

omit FA in
lemma acceptable : germ a.M := Push.Loops.matrix_diff a.germ_M

/-- The full real position-space weight, now a literal multi-gauge ticket. -/
def relative (a:Axes G n A J) : Ticket (Transverse G n) := MultiGauge.Stack.exponential (MultiGauge.Stack.advancing (Slice.W G n)) * MultiGauge.Stack.rise (Real.exp ∘ Slice.haar G n) * MultiGauge.Stack.rise (Gem.germ_det a.M)
omit FA in
lemma priced_zero : incline a.relative := by
  unfold relative incline; rw [map_mul,map_mul, MultiGauge.Stack.initial];
  have h (kF:L→ℝ): (PowerSeries.constantCoeff (Ω kF)).val=fun _=> kF 0 := by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, MultiGauge.Stack.rise,PowerSeries.coeff_mk]; exact funext fun _=> PertExtension.Series.Radial.jet_zero ..
  have he (X:L→ℝ)(hx:X 0=1): PowerSeries.constantCoeff (Ω X)=1:= Subtype.ext ((h X).trans (funext fun y=> hx))
  rw [he,he,one_mul,one_mul]; · simp [Gem.germ_det, flat_M]
  simp [Slice.haar_zero]

local notation "Φ" => Y (Ξ * Ω (Real.exp ∘ Slice.haar G n))
local notation "v" => exp0 b Q
lemma moves : promote δ S = Φ ★ v := by
  have hy := Boson.bills_even (J:=J) a.X; obtain ⟨h,h'⟩ := a.real_first; let τ := Y Υ; 
  rw [Wick.Formal.pull_exp a.R a.tieR, a.exponent_body,
      Wick.Formal.exp_add ((Wick.Formal.even b).add_mem (hy Υ) (hy Lφ)) (Fermion.even a.X _) (by rw [Pi.add_apply,h,h',zero_add]) (exp_first a.X _ a.flat_M),
      Wick.Formal.exp_add (hy Υ) (hy Lφ) h h',
      Boson.tab_mul,tab_exp,Boson.analytic a.X _ (haar_smooth _ _), Gem.inkExp (eased a.X) (eased_p a.X) (haar_smooth G n) haar_zero];
  rw [Boson.analytic a.X _ (show germ (Real.exp ∘ Slice.haar G n) from Real.contDiff_exp.contDiffAt.comp 0 (haar_smooth G n))]

omit FA in
lemma gauge_slot (α : Ticket (Transverse G n)) : (Φ ★ v) ★ Y α = (Φ ★ Y α) ★ v := by rw [Formal.assoc, ← Formal.central (bills_even a.X α), Formal.assoc]

variable [DecidableEq A]

lemma wash (α : Ticket (Transverse G n)) : promote (Wg A J) ((promote δ S) ★ Y α) = Y (a.relative * α) := by
  let V:=exp0 b Q; let K:= Ξ * Ω (Real.exp ∘ Slice.haar G n); let x := K*α
  have h := frame_time (Y x) V (bills_alone _ _) (bills_funded _ _) (Formal.exponent_ok (valid a.X _ a.germ_M));
  rw [a.moves,a.gauge_slot, ← Boson.tab_mul]; rw [h]; unfold relative; rw [mul_right_comm K, Boson.tab_mul a.X x, Boson.analytic a.X (Gem.germ_det a.M) (Gem.det_germ a.acceptable) ]; rw [show promote (Wg A J) V = _ from unbill a.X a.flat_M a.acceptable]
end Axes
end YM.FVA2.Slice
