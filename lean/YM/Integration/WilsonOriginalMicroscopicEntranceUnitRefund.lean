import YM.Integration.WilsonOriginalMicroscopicEntranceFlatPublic
import YM.Integration.WilsonOriginalMicroscopicEntranceHalo

/-! Beginning with the actual enrolled coordinate at K, the charge per
slot cancels its unit at f before the remaining optical ratio is billed. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceUnitRefund
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
open scoped Classical BigOperators


open WilsonReflectedAffordableArm (charge projectionBill projected)
open WilsonOriginalMicroscopicEntranceGridBalance (coord slotFare)
variable {G:Gauge}(R:Run G)
local notation "CF" => R.family
local notation "J" => Stock.census (Fin 3)


private theorem units_norm (d:Fin 3→ℕ)(K:ℕ)(s:(J).Mode):
    ‖units R d K s‖=∏a∈s.val,(((CF).S.a K)^(d a))⁻¹:=by
  simp [units,norm_prod,Real.norm_of_nonneg ((CF).S.a_pos K).le]

theorem product (d:Fin 3→ℕ)(f K:ℕ)(M:Fin 3→ℝ)(s:(J).Mode):
    ‖units R d K s‖*peak R d K (fun a=>((CF).S.a f)^(d a)*M a) s.val=
    2*∏a∈s.val,(((CF).S.a f/(CF).S.a K)^(d a))*(loss R (d a) K*M a):=by
  rw [units_norm,peak,mul_left_comm _ (2:ℝ),←Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  rw [div_pow,div_eq_mul_inv]
  ring

theorem supplied (d:Fin 3→ℕ){f K:ℕ}(v:∀a:Fin 3,(CF).label (d a))(V:Fin 3→ℝ)
    (earned:∀a,slotFare R d f K v a≤((CF).S.a f)^(d a)*V a):
    ∀a,((CF).labels.level (d a)).coeffSize (v a)≤((CF).S.a f)^(d a)*
      (V a/(hike CF K f rate*(1+4*stock CF K))):=by
  intro a
  have pos:0<hike CF K f rate*(1+4*stock CF K):=mul_pos (hike_pos CF K f rate) (by
    have stock₀:0 ≤ stock CF K:=zero_le_one.trans ((CF).path.levels.params K).columns_ge
    linarith)
  rw [←mul_div_assoc,le_div_iff₀ pos]
  exact (by simpa only [slotFare,mul_comm,mul_left_comm,mul_assoc] using earned a)

theorem original (d:Fin 3→ℕ){f K:ℕ}(v:∀a:Fin 3,(CF).label (d a))(V:Fin 3→ℝ)
    (earned:∀a,slotFare R d f K v a≤((CF).S.a f)^(d a)*V a)(s:(J).Mode):
    let Q:=fun a=>V a/(hike CF K f rate*(1+4*stock CF K))
    (∀a,((CF).labels.level (d a)).coeffSize (v a)≤((CF).S.a f)^(d a)*Q a) ∧
    ‖units R d K s‖*peak R d K (fun a=>((CF).S.a f)^(d a)*Q a) s.val=
      2*∏a∈s.val,(((CF).S.a f/(CF).S.a K)^(d a))*(loss R (d a) K*Q a):=
  ⟨supplied R d v V earned,product R d f K _ s⟩

end YM.Integration.WilsonOriginalMicroscopicEntranceUnitRefund
end
