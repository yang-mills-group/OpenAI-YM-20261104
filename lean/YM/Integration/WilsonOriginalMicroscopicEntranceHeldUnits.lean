import YM.Integration.WilsonOriginalMicroscopicEntranceHaloIncome

/-! The optical cost on the genuine conditional law at the requested held field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHeldUnits
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner OPE.Therm
open WilsonOriginalMicroscopicGuardedTrial WilsonOriginalMicroscopicGuardedWallet
open Extra.Histories Extra.Multi Push.AbsoluteSums.Animals
open WilsonOriginalMicroscopicEntranceFiling (units)
open WilsonOriginalMicroscopicEntranceGridBalance (slotFare)
open WilsonOriginalMicroscopicEntranceOpticalUnits (pole rank dye fare)
open WilsonOriginalMicroscopicGuardedFlat (peak count)
open Trace.Physical.Germ Trace.Physical.GermGraph
open WilsonOriginalMicroscopicGuardedPosterior (gross)
open scoped BigOperators Classical

variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ)

local notation "CF" => R.family
local notation "J" => Stock.census (Fin 3)
local notation "H" i:max => (CF).path.levels.clock.hatBeta i
local notation "mesh" i:max => (CF).S.a i


theorem gross_bound {N per K:ℕ}(live:K ≤ N)(v:∀a:Fin 3,(CF).label (d a))(M:Fin 3→ℝ)
    (charge:∀a,((CF).labels.level (d a)).coeffSize (v a) ≤ M a)(s:(J).Mode):
    gross R d N per K v s.val ≤ peak R d K M s.val:=by
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.prod_le_prod
  · exact fun a _=>add_nonneg (norm_nonneg _) (mul_nonneg (zero_le_one.trans (BasisCost.price_pos _)) (BasisCost.coeff_nonneg _))
  · exact fun a _=>(one R d N per K live v a).trans (mul_le_mul_of_nonneg_left (charge a) (nonneg R _ _))

theorem priced {N per f K t:ℕ}(live:K ≤ N)(up:f ≤ K)(housing:mesh f/mesh K ≤ (H K)^t)
    (v:∀a:Fin 3,(CF).label (d a))(V:Fin 3→ℝ)(vp:∀a,0 ≤ V a)
    (earned:∀a,slotFare R d f K v a ≤ (mesh f)^(d a)*V a)(s:(J).Mode):
    ‖units R d K s‖*gross R d N per K v s.val ≤ fare R d V s*(H K)^(pole R d t s):=by
  let M:=fun a=>(mesh f)^(d a)*(V a/(hike CF K f rate*(1+4*stock CF K)))
  have pay:=WilsonOriginalMicroscopicEntranceUnitRefund.supplied R d v V earned
  exact (mul_le_mul_of_nonneg_left (gross_bound R d live v M pay s) (norm_nonneg _)).trans
    (WilsonOriginalMicroscopicEntranceOpticalUnits.original R d up housing V vp s)

theorem original {N per f K t i:ℕ}(live:K ≤ N)(up:f ≤ K)(before:i+1 ≤ K)(housing:mesh f/mesh K ≤ (H K)^t)
    (o:Fin 3→Site ((CF).side K per))(v:∀a:Fin 3,(CF).label (d a))(V:Fin 3→ℝ)(vp:∀a,0 ≤ V a)
    (earned:∀a,slotFare R d f K v a ≤ (mesh f)^(d a)*V a)(s:(J).Mode)(W:Config G ((CF).side i per)):
    let μ:=WilsonMacroscopicRichFlatPosteriorLaw.law R N per before W
    let E:=SelectedCofactorAnchoredRegister.hot (G:=G) ((CF).path.rep N per K).p.threshold (footprint R d per K o s.val)
    let event:=gap R d N per K o v s.val
    units R d K s*actualTransport CF (N:=N) event ((Nat.le_succ i).trans before) W=units R d K s*(∫U,event U ∂μ) ∧
      ‖units R d K s*actualTransport CF (N:=N) event ((Nat.le_succ i).trans before) W‖ ≤ 
        (fare R d V s*(H K)^(pole R d t s))*μ.real E:=by
  intro μ E event
  obtain ⟨read,fee⟩:=WilsonOriginalMicroscopicGuardedHeld.original R d live before o v s.val W
  constructor
  · exact congrArg (units R d K s * ·) read
  · rw [norm_mul]
    calc
      _ ≤ ‖units R d K s‖*(gross R d N per K v s.val*μ.real E):=mul_le_mul_of_nonneg_left fee (norm_nonneg _)
      _=(‖units R d K s‖*gross R d N per K v s.val)*μ.real E:=(mul_assoc ..).symm
      _ ≤ _:=mul_le_mul_of_nonneg_right (priced R d (per:=per) live up housing v V vp earned s) measureReal_nonneg

end YM.Integration.WilsonOriginalMicroscopicEntranceHeldUnits
end
