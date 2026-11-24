import YM.Integration.WilsonThermometerUnitFilingWeakRoom
import YM.Integration.WilsonOriginalCompoundStrip

/-! Enrol the cover and outgoing group-word apertures at the same original election. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingWeakStrip
open Finset Lattice Laurent Bloch Metric Exterior Precision RG Next.Free Work.F08
open AllOrder AllOrder.Floe Org PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonOriginalCompoundStrip
open scoped BigOperators Classical
variable {G:Gauge}

def trial (Q:Request G)(K:KernelChoices)(x H:ℕ):ℝ:=
  min 1 (min (Q.radius K x H) (WilsonThermometerUnitFilingWeakRoom.width G K x)/(16*max 1 (Q.multiplier H)))

theorem trial_pos (Q:Request G)(K:KernelChoices)(x H:ℕ):0<trial Q K x H:=
  lt_min zero_lt_one (div_pos (lt_min (Q.positive ..) (WilsonThermometerUnitFilingWeakRoom.width_pos ..))
    (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one (le_max_left ..))))

def cross (Q:Request G)(K:KernelChoices)(x:ℕ):ℕ:=
  Nat.ceil (1+∑i:WilsonThermometerUnitFilingWeakRoom.Steps x,(trial Q K i.1 i.2)⁻¹)

def enrolled (Q:Request G):Request G where
  radius K x H :=min (Q.radius K x H) (WilsonThermometerUnitFilingWeakRoom.width G K x)
  positive K x H:=lt_min (Q.positive K x H) (WilsonThermometerUnitFilingWeakRoom.width_pos G K x)
  multiplier H:=max 1 (Q.multiplier H)
  grows H:=zero_lt_one.trans_le (le_max_left 1 (Q.multiplier H))
  entrance K x P:=max (Q.entrance K x P) (max (WilsonThermometerUnitFilingWeakRoom.floor G K x) (cross Q K x))

theorem line (Q:Request G)(K:KernelChoices)(x H:ℕ):
    trial Q K x H≤WilsonThermometerUnitFilingWeakRoom.width G K x:=by
  have h:1≤16*max 1 (Q.multiplier H):=by linarith [le_max_left 1 (Q.multiplier H)]
  exact (min_le_right ..).trans ((div_le_self (le_of_lt (lt_min (Q.positive ..)
    (WilsonThermometerUnitFilingWeakRoom.width_pos ..))) h).trans (min_le_right ..))

theorem inherited (Q:Request G)(K:KernelChoices)(x j H:ℕ)(jrow:j≤x+1)(hr:H≤x+1)
    {L:Side}(purchase:cross Q K x≤L.val)(s:ℝ)(small:s≤1):
    s/(L.val:ℝ)≤trial Q K j H:=by
  let i:WilsonThermometerUnitFilingWeakRoom.Steps x:=(⟨j,by omega⟩,⟨H,by omega⟩)
  have he:(trial Q K i.1 i.2)⁻¹≤∑k:WilsonThermometerUnitFilingWeakRoom.Steps x,(trial Q K k.1 k.2)⁻¹:=
    single_le_sum (fun k _=>(inv_pos.mpr (trial_pos Q K k.1 k.2)).le) (mem_univ i)
  have hp:1+(∑k:WilsonThermometerUnitFilingWeakRoom.Steps x,(trial Q K k.1 k.2)⁻¹)≤(L.val:ℝ):=
    (Nat.le_ceil _).trans (by exact_mod_cast purchase)
  have fee:(trial Q K i.1 i.2)⁻¹≤(L.val:ℝ):=by linarith
  have positive:0<(L.val:ℝ):=by positivity
  have hc:(L.val:ℝ)⁻¹≤trial Q K j H:=by simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr (trial_pos Q K i.1 i.2)) fee
  exact (div_le_div_of_nonneg_right small positive.le).trans (by simpa only [one_div] using hc)

theorem date (Q:Request G)(R:Run G)(p:WilsonOriginalProfileStrip.Filed
    (WilsonOriginalCompoundStrip.programme (enrolled Q)) R.kit)(i H:ℕ)(fit:H≤R.alloy.B.a.clock.J i):
    let x:=R.alloy.B.a.clock.J i
    let K:=R.metals.p.kernel
    let μ:=trial Q K x H
    let L:=R.alloy.B.a.clock.factor x
    Q.entrance K x (R.metals.p.profile x)≤L.val ∧
    WilsonThermometerUnitFilingWeakRoom.floor G K x≤L.val ∧ 0<μ ∧ μ≤1 ∧
    μ≤WilsonThermometerUnitFilingWeakRoom.width G K x ∧
    Real.exp (μ⁻¹^2)≤R.alloy.B.a.clock.hatBeta i ∧
    (∀j H',j≤x+1→H'≤x+1→μ/(L.val:ℝ)≤trial Q K j H'):=by
  have z:=WilsonOriginalCompoundStrip.date (enrolled Q) R p i H fit
  obtain ⟨h,hp,hs,-,hh,-⟩:=z
  refine ⟨(le_max_left ..).trans h,((le_max_left ..).trans (le_max_right ..)).trans h,hp,hs,line ..,hh,?_⟩
  intro j H' hj he
  exact inherited Q _ _ j H' hj he (((le_max_right ..).trans (le_max_right ..)).trans h) _ hs

end YM.Integration.WilsonThermometerUnitFilingWeakStrip
