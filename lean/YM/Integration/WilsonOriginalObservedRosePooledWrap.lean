import YM.Integration.WilsonOriginalObservedRoseVanePurse

/-! Restoring the public reporting wage on the actual unscaled fitted column. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRosePooledWrap
open Function Filter Finset RG Lattice Wilson Source Labels Next.Rank Next.Rank.Price Next.Rank.Atlas
open Next.Rank.Station Further.CorrectedLift Cells Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open Spec OPE OPE.Orbits RG17 PhysMS PhysMS.Frame Maxwell XSpace XSpace.Normalize WilsonPositionCapTransport
open WilsonOlderFreshSoftSocketVane (quotaFare)
open scoped Classical BigOperators Topology

variable {G:Gauge}(R:Run G){f:Extraction.Order}{Y:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
    {S:Table R.family.book}
local notation "C" => R.family
local notation "road" => R.family.path.levels

open WilsonOriginalObservedRoseMeshHeight (variation)
open WilsonOriginalMicroscopicGuardedPage (wrapCost)
open Extra.Histories.Motion (orbitCost orbitCost_one_le)
open WilsonCapturedPrimaryCoreBill (wrapFee)
open Trace.Physical.Germ
open Source
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "a" => R.family.S.a

def allowance (d:ℕ):ℝ:=1+wrapFee ((C).labels.level d) (C).params*Real.exp 200

theorem positive (d:ℕ):1≤allowance R d:=by
  have h:0≤wrapFee ((C).labels.level d) (C).params:=
    mul_nonneg (Nat.cast_nonneg _) (germ_close ((C).labels.level d) (C).params).choose_spec.1.le
  unfold allowance
  linarith only [mul_nonneg h (Real.exp_nonneg 200)]

theorem charged (d j K:ℕ)(width:((road).budget j).supportExponent≤100)
    (stock:((road).params j).columns≤β K): |1+wrapCost R d j|≤allowance R d*(β K):=by
  let fee:=wrapFee ((C).labels.level d) (C).params
  have hp:0≤fee:=mul_nonneg (Nat.cast_nonneg _) (germ_close ((C).labels.level d) (C).params).choose_spec.1.le
  have ep:Real.exp (2*((road).budget j).supportExponent)≤Real.exp 200:=
    Real.exp_le_exp.mpr (by linarith only [width])
  have pos:0≤((road).params j).columns:=zero_le_one.trans ((road).params j).columns_ge
  have wp:0≤wrapCost R d j:=mul_nonneg (mul_nonneg hp (Real.exp_nonneg _)) pos
  have paid:wrapCost R d j≤fee*Real.exp 200*β K:=
    mul_le_mul (mul_le_mul_of_nonneg_left ep hp) stock pos (mul_nonneg hp (Real.exp_nonneg _))
  rw [abs_of_nonneg (by linarith only [wp]),allowance,add_mul,one_mul]
  exact add_le_add ((road).fits.delayed K).le paid

theorem original {n:ℕ}(d:Fin n→ℕ)(i:Fin n)(j N per K:ℕ)(Y:(C).label (d i))
    (width:((road).budget j).supportExponent≤100)(stock:((road).params j).columns≤β K)
    {fare:ℝ}(receipt:Next.UVStress.quota (C) (d i) j N per Y≤(a j)^(d i)*fare):
    variation R d j N per i Y ≤
      (2*orbitCost ((C).labels.level (d i))*allowance R (d i))*(β K)*fare:=by
  let bill:=Next.Rank.Spindle.paid (C) (d i) j N per Y
  have qp:0≤Next.UVStress.quota (C) (d i) j N per Y:=by
    unfold Next.UVStress.quota Frame.coeffSize
    exact Finset.sum_nonneg fun _ _=>norm_nonneg _
  have ap:0<(a j)^(d i):=pow_pos ((C).S.a_pos _) _
  have same:bill*(a j)^(d i)=Next.UVStress.quota (C) (d i) j N per Y:=WilsonMatrixTicketLanesQuota.quota Y j N per
  have low:0≤bill:=(nonneg_of_mul_nonneg_left (same.symm ▸ qp) ap)
  have price:bill≤fare:=(mul_le_mul_iff_of_pos_right ap).mp (same.le.trans (receipt.trans_eq (mul_comm _ _)))
  let Ω:=orbitCost ((C).labels.level (d i))
  have op:0≤2*Ω:=mul_nonneg (by norm_num) (zero_le_one.trans (orbitCost_one_le _))
  change |2*Ω*((1+wrapCost R (d i) j)*bill)|≤_
  rw [abs_mul,abs_of_nonneg op,abs_mul,abs_of_nonneg low]
  calc _≤2*Ω*(allowance R (d i)*(β K)*fare):=mul_le_mul_of_nonneg_left
         (mul_le_mul (charged R (d i) j K width stock) price low
           (mul_nonneg (zero_le_one.trans (positive R (d i))) (zero_le_one.trans ((road).fits.delayed K).le))) op
       _=_:=by ring

end YM.Integration.WilsonOriginalObservedRosePooledWrap
end
