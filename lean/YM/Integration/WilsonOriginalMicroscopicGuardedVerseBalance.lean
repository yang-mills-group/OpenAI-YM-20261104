import YM.Integration.WilsonOriginalMicroscopicGuardedHeld
import YM.Integration.WilsonReceivedCanonicalVersePosterior
import YM.Integration.WilsonLimitConstruction.FundedWilsonTransportMoments

/-! The signed difference between the fixed canonical portfolio and the
guarded physical product at every true earlier held field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicGuardedVerseBalance
open Filter Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Extra.Multi
open PhysicalNext.Repeat.Legato OPE.Therm Push.AbsoluteSums.Animals
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Carp Pert.Asymptotics
open WilsonPointChildFiledPress OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonReceivedCanonicalVersePosterior (word)
open WilsonOriginalMicroscopicGuardedTrial
open Planned.PrimaryIntegral295 Place Film Carrier
open scoped BigOperators Classical

variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ){h:Fin 3→ℕ}
variable (κ:(a:Fin 3)→Knob (h a))(pt:Fin 3→Chamber)
variable (N p K:ℕ)(live:K≤N)(o:Fin 3→Site (R.family.side K p))(v:∀a:Fin 3,R.family.label (d a))(s:Finset (Fin 3))
local notation "Y" => gap R d N p K o v s
local notation "X" => Config G (R.family.side K p)
local notation "ψ₀" => face (guarded R d N p K o v) s
local notation "ψ₁" => face (raw R d N p K o v) s
local notation "S₀" => R.family.path.rep N p K

def printed {i:ℕ}(prior:i≤K)(U:Config G (R.family.side i p)):ℂ:=
  ∑q:Selection R d s,weight R d N p K v s q*actualTransport R.family (N:=N)
       (word R d κ pt (regulatorRun R.family N p K) o s q) prior U

include live in
theorem original {i:ℕ}(prior:i≤K)(U:Config G (R.family.side i p)):
    printed R d κ pt N p K o v s prior U-actualTransport R.family (N:=N) ψ₀ prior U=
      actualTransport R.family (N:=N) Y prior U:=by
  have income:=WilsonReceivedCanonicalVersePosterior.original R d κ pt N p K live v o s i prior U
  have same:ψ₁=(fun W:X=>∏a:s,WilsonPositionProgramBlockedTrialAddBack.uncut R (d a) N p K (o a) (v a) W):=by
    funext W
    exact (Finset.prod_coe_sort s (fun a=>WilsonPositionProgramBlockedTrialAddBack.uncut R (d a) N p K (o a) (v a) W)).symm
  have cash:=unary R d N p K o v
  letI:IsProbabilityMeasure (scene R.family.path N p K):=probability R.makes.wilson live
  have pay (F:Fin 3→X→ℂ)(meas:∀a,Measurable (F a))(close:∀a W,‖F a W‖≤cap R d N p K v a):
      Integrable (face F s) (scene R.family.path N p K):=by
    apply Integrable.of_bound (Finset.measurable_prod s (fun a _=>meas a)).aestronglyMeasurable (∏a∈s,cap R d N p K v a)
    apply ae_of_all
    intro W
    change ‖∏a∈s,F a W‖≤_
    rw [norm_prod]
    exact Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun a _=>close a W)
  have left:=pay _ (fun a=>(cash a).2.1) (fun a W=>((cash a).2.2 W).2)
  have right:=pay _ (fun a=>(cash a).1) (fun a W=>((cash a).2.2 W).1)
  have linear:=ActualWilsonAbsoluteTransport.sub R.family R.makes live
    (WilsonLimitConstruction.FundedWilsonTransportMoments.weighted R.family R.makes live left)
    (WilsonLimitConstruction.FundedWilsonTransportMoments.weighted R.family R.makes live right) prior
  rw [←same] at income
  exact (congrArg (fun z=>z-actualTransport R.family (N:=N) ψ₀ prior U) income.symm).trans
    (congrFun linear U).symm

include live in
theorem held {i:ℕ}(before:i+1≤K)(U:Config G (R.family.side i p)):
    let age: i≤K:=(Nat.le_succ i).trans before
    let E:=SelectedCofactorAnchoredRegister.hot (G:=G) (S₀).p.threshold (footprint R d p K o s)
    ‖printed R d κ pt N p K o v s age U-actualTransport R.family (N:=N) ψ₀ age U‖≤
      WilsonOriginalMicroscopicGuardedPosterior.gross R d N p K v s*
        (WilsonMacroscopicRichFlatPosteriorLaw.law R N p before U).real E:=by
  dsimp only
  rw [original R d κ pt N p K live o v s]
  exact (WilsonOriginalMicroscopicGuardedHeld.original R d live before o v s U).2

end YM.Integration.WilsonOriginalMicroscopicGuardedVerseBalance
end
