import YM.Integration.WilsonOriginalMicroscopicEntranceOpticalUnits
import YM.Integration.WilsonOriginalMicroscopicEntranceUnitRefund
import YM.Integration.WilsonOriginalCoordinateExposure

/-! A fixed power from the actual optical geometry and the finite true
stencil pays the entire physical unit on every original face. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceRawSalary
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



open private inverse_hike from YM.Integration.WilsonOriginalMicroscopicEntranceOpticalUnits
open WilsonOriginalMicroscopicEntranceGridRow (factor)
local notation "mesh" i:max => (CF).S.a i

theorem original (d:Fin 3→ℕ){f K t:ℕ}(up:f≤K){H:ℝ}(housing:(mesh f)/(mesh K)≤H^t)
    (v:∀a:Fin 3,(CF).label (d a))(V:Fin 3→ℝ)(vp:∀a,0≤V a)
    (earned:∀a,slotFare R d f K v a≤(mesh f)^(d a)*V a)(a:Fin 3):
    ((CF).labels.level (d a)).coeffSize ((factor R d K a) • (v a))≤H^(t*(d a+1))*V a:=by
  have issue:=WilsonOriginalMicroscopicEntranceUnitRefund.supplied R d v V earned a
  let ratio:=(mesh f)/(mesh K)
  let budget:=hike CF K f rate*(1+4*stock CF K)
  have inv:budget⁻¹≤ratio:=inverse_hike R up
  have sk:0 < mesh K:=(CF).S.a_pos K
  have sf:0 < mesh f:=(CF).S.a_pos f
  have ratio₀:0≤ratio:=(div_pos sf sk).le
  have take:((CF).labels.level (d a)).coeffSize ((factor R d K a) • (v a))=
      ((mesh K)^(d a))⁻¹*((CF).labels.level (d a)).coeffSize (v a):=by
    unfold Labels.Frame.coeffSize
    simp only [Pi.smul_apply,norm_smul,Finset.mul_sum]
    simp only [WilsonOriginalMicroscopicEntranceGridRow.factor,norm_inv,norm_pow,Complex.norm_real,Real.norm_of_nonneg sk.le]
  rw [take]
  calc
    _≤((mesh K)^(d a))⁻¹*((mesh f)^(d a)*(V a/budget)):=mul_le_mul_of_nonneg_left issue (inv_nonneg.mpr (pow_nonneg sk.le _))
    _=ratio^(d a)*(V a*budget⁻¹):=by rw [show ratio=(mesh f)/(mesh K) from rfl,div_pow];ring
    _≤ratio^(d a)*(V a*ratio):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left inv (vp a)) (pow_nonneg ratio₀ _)
    _=ratio^(d a+1)*V a:=by rw [pow_succ];ring
    _≤(H^t)^(d a+1)*V a:=mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ratio₀ housing _) (vp a)
    _=H^(t*(d a+1))*V a:=by rw [pow_mul]

end YM.Integration.WilsonOriginalMicroscopicEntranceRawSalary
end
