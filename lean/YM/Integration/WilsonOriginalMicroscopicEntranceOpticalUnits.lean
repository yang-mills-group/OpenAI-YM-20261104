import YM.Integration.WilsonOriginalMicroscopicEntranceUnitRefund
import YM.Integration.WilsonOriginalCoordinateExposure

/-! A fixed power from the actual optical geometry and the finite true
stencil pays the entire physical unit on every original face. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceOpticalUnits
open Function Filter Set MeasureTheory Analysis Table Extraction Lattice RG Wilson Labels Source
open GapsContact GapsContact.Seams GapsContact.Stamps GapsContact.Ascent
open Push Extra.Histories Bid Spec Ascent Power Stamps Trace Trace.Verse Trace.Terrace Trace.Pilot
open Trace.Over MergeProof.East Further.CorrectedLift Next.Rank.Price Next.Rank Next.Rank.East
open Next.Rank.Station Ward Climb OPE OPE.Levy PhysicalNext.Repeat.Legato Pert.Asymptotics
open PhysicalNext OPE.Therm Push.AbsoluteSums.Animals Next.Foundations Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open WilsonOriginalNullCorridor WilsonOriginalNullPlacedGermMap RG05Readout RG05Readout.Address
open WilsonPositionProgramBlockedPublicExperiment WilsonThermometerUnitFilingFourPool
open WilsonOriginalMicroscopicGuardedNomination WilsonOriginalMicroscopicGuardedReporters
open WilsonOriginalMicroscopicGuardedTrial WilsonOriginalMicroscopicGuardedWallet
open WilsonOriginalMicroscopicGuardedPage
open WilsonOriginalMicroscopicGuardedPageSchool WilsonAddressedRestartedColumn
open WilsonPositionProgramOriginalBlockedTrial RG05Readout.Records
open WilsonOriginalMicroscopicGuardedFlat (peak)
open WilsonOriginalMicroscopicGuardedWallet (loss)
open WilsonOriginalMicroscopicEntranceFiling (units)
open Extra.Histories Extra.Multi Push.AbsoluteSums.Animals
open scoped Classical Topology BigOperators
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Carp
open WilsonPointChildFiledPress OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonOriginalMicroscopicEntranceGridRow (pin)
open WilsonOriginalMicroscopicEntranceGridStock (account Filed)
open WilsonOriginalMicroscopicEntranceFiling (units)
open WilsonOriginalMicroscopicEntranceSockets (read)
open WilsonOriginalMicroscopicGuardedTrial (raw guarded gap)
open WilsonOriginalMicroscopicGuardedGridSchool (Placed)
open WilsonOriginalMicroscopicGuardedFlat (peak)
open WilsonOriginalMicroscopicGuardedWallet (loss)
open WilsonOriginalMicroscopicEntranceFiling (units)
open Extra.Histories Extra.Multi Push.AbsoluteSums.Animals
open scoped Classical BigOperators


open WilsonReflectedAffordableArm (charge projectionBill projected)
open WilsonOriginalMicroscopicEntranceGridBalance (coord slotFare)
variable {G:Gauge}(R:Run G)
local notation "CF" => R.family
local notation "J" => Stock.census (Fin 3)



def dye (d:ℕ):ℝ:=1+BasisCost.price ((CF).localSection d)
def rank (d:ℕ):ℕ:=BasisCost.slots ((CF).labels.level d)
def pole (d:Fin 3→ℕ)(t:ℕ)(s:(J).Mode):ℕ:=∑a∈s.val,(t*(d a+1)+rank R (d a))
def fare (d:Fin 3→ℕ)(V:Fin 3→ℝ)(s:(J).Mode):ℝ:=2*∏a∈s.val,dye R (d a)*V a
local notation "H" i:max => (CF).path.levels.clock.hatBeta i
local notation "mesh" i:max => (CF).S.a i

private theorem material (d K:ℕ):loss R d K≤dye R d*(H K)^(rank R d):=by
  have β:1≤H K:=((CF).path.levels.fits.delayed K).le
  have price:0≤BasisCost.price ((CF).localSection d):=zero_le_one.trans (BasisCost.price_pos _)
  apply mul_le_mul_of_nonneg_left _ (by change 0≤1+BasisCost.price ((CF).localSection d);linarith)
  have th:((CF).path.levels.budget K).threshold⁻¹≤H K:=by
    rw [←min_eq_left ((CF).path.levels.budget K).threshold_le]
    exact WilsonOriginalCoordinateExposure.threshold R K
  exact pow_le_pow_left₀ ((zero_le_one:0≤(1:ℝ)).trans (le_max_left ..)) (max_le β th) _

private theorem inverse_hike {f K:ℕ}(up:f≤K):
    (hike CF K f rate*(1+4*stock CF K))⁻¹≤ mesh f/mesh K:=by
  have dpos:=div_pos ((CF).S.a_pos K) ((CF).S.a_pos f)
  have small:mesh K/mesh f≤1:=(div_le_one ((CF).S.a_pos f)).mpr ((CF).S.strictAnti.antitone up)
  have close:mesh K/mesh f≤hike CF K f rate:=by
    calc
      _=(mesh K/mesh f)^(1:ℝ):=(Real.rpow_one _).symm
      _≤_:=Real.rpow_le_rpow_of_exponent_ge dpos small (by norm_num [Trace.Physical.GermGraph.rate])
  have st:0 ≤ stock CF K:=zero_le_one.trans ((CF).path.levels.params K).columns_ge
  have h:=hike_pos CF K f rate
  have one:1≤1+4*stock CF K:=by linarith
  have rise:=close.trans (le_mul_of_one_le_right h.le one)
  calc
    _≤(mesh K/mesh f)⁻¹:=(inv_le_inv₀ (dpos.trans_le rise) dpos).mpr rise
    _=mesh f/mesh K:=inv_div _ _

theorem original (d:Fin 3→ℕ){f K t:ℕ}(up:f≤K)(housing:mesh f/mesh K≤(H K)^t)(V:Fin 3→ℝ)(vp:∀a,0≤V a)(s:(J).Mode):
    let Q:=fun a=>V a/(hike CF K f rate*(1+4*stock CF K))
    ‖units R d K s‖*peak R d K (fun a=>(mesh f)^(d a)*Q a) s.val≤fare R d V s*(H K)^(pole R d t s):=by
  intro Q
  have β:1≤H K:=((CF).path.levels.fits.delayed K).le
  have tpos:=div_pos ((CF).S.a_pos f) ((CF).S.a_pos K)
  have st:0 ≤ stock CF K:=zero_le_one.trans ((CF).path.levels.params K).columns_ge
  have hpos:=hike_pos CF K f rate
  have room:0<hike CF K f rate*(1+4*stock CF K):=mul_pos hpos (by linarith)
  have qp (a):0≤Q a:=div_nonneg (vp a) room.le
  have each (a:Fin 3):(mesh f/mesh K)^(d a)*(loss R (d a) K*Q a)≤
      (dye R (d a)*V a)*(H K)^(t*(d a+1)+rank R (d a)):=by
    have refund:Q a≤V a*(H K)^t:=by
      rw [show Q a=V a*(hike CF K f rate*(1+4*stock CF K))⁻¹ from div_eq_mul_inv ..]
      exact mul_le_mul_of_nonneg_left ((inverse_hike R up).trans housing) (vp a)
    have high:0≤dye R (d a)*(H K)^(rank R (d a)):= (WilsonOriginalMicroscopicGuardedWallet.nonneg R (d a) K).trans (material R _ _)
    have raised:=mul_le_mul (material R (d a) K) refund (qp a) high
    calc
      _≤((H K)^t)^(d a)*((dye R (d a)*(H K)^(rank R (d a)))*(V a*(H K)^t)):=
        mul_le_mul (pow_le_pow_left₀ tpos.le housing _) raised
          (mul_nonneg (WilsonOriginalMicroscopicGuardedWallet.nonneg R (d a) K) (qp a))
          (pow_nonneg (pow_nonneg (zero_le_one.trans β) _) _)
      _=_:=by rw [pow_add,pow_mul,pow_succ];ring
  rw [WilsonOriginalMicroscopicEntranceUnitRefund.product R d f K Q s]
  calc
    _≤2*∏a∈s.val,(dye R (d a)*V a)*(H K)^(t*(d a+1)+rank R (d a)):=by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.prod_le_prod (fun a _=>mul_nonneg (pow_nonneg tpos.le _)
        (mul_nonneg (WilsonOriginalMicroscopicGuardedWallet.nonneg R (d a) K) (qp a))) fun a _=>each a
    _=_:=by rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum];unfold fare pole;ring

end YM.Integration.WilsonOriginalMicroscopicEntranceOpticalUnits
end
