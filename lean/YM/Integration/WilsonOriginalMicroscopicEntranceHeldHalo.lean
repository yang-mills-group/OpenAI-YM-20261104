import YM.Integration.WilsonOriginalDecoderPosterior
import YM.Integration.WilsonOriginalMicroscopicEntranceHaloIncome

/-! The actual conditional probability of any finite failed support, including the microscopic cutoff. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHeldHalo
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner OPE.Therm
open WilsonOriginalMicroscopicGuardedTrial
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){N per m k i:ℕ}(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)
    (Ψ:∀j,Rep G (R.family.side j per))(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    {K:ℕ}(cut:K≤N)(top:Topline (Ψ N) (R.alloy.B.a.clock.forcedAllowance N))
    (simple:G.Simple)(way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q:D.Tab R.rolls)(ticket:TicketP R.alloy R.kit D Q){u:ℕ}(floor:m ≤ u)(ui:u ≤ i)
    (fixed:WilsonSingleHardRadius.first R simple ≤ u)(cap:WilsonCenteredCaptureClock.first R simple ≤ K)
local notation "H" => R.alloy.B.a.clock.hatBeta K
local notation "param" => R.alloy.B.a.budget K
local notation "μ" before:max W:max => WilsonMacroscopicRichFlatPosteriorLaw.law R N per before W

def spring (i N per:ℕ)(W:Config G (R.family.side i per)):ℝ:=
  (Real.exp (WilsonOriginalDecoderSpring.bill (R.family.path.levels.clock.op i per)
    (R.family.path.β N per (i+1)) W))^2

include course cut top way ticket floor ui fixed cap in
theorem original (p:ℕ){tol:ℝ}(positive:0<tol)
    (late:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple p positive)).choose≤K)
    (before:i+1≤K)(X:Support (R.family.side K per))(V:Config G (R.family.side i per)):
    (μ before V).real (SelectedCofactorAnchoredRegister.hot (G:=G)
      (R.family.path.rep N per K).p.threshold X) ≤ spring R i N per V*
        ((X.card:ℝ)*(4*Real.exp ((param).supportExponent+2))*(tol/H^p)):=by
  let E:=SelectedCofactorAnchoredRegister.hot (G:=G) (R.family.path.rep N per K).p.threshold X
  have hm:MeasurableSet E:=SelectedCofactorAnchoredRegister.measurable ..
  let Y:=E.indicator (fun _=>(1:ℂ))
  have borel:Measurable Y:=measurable_const.indicator hm
  have ub:=ui.trans ((Nat.le_succ i).trans before)
  have point:(Ψ K).p=R.family.path.levels.budget K:=(course.1.walk K (floor.trans ub) cut).truep.point
  have housed:(Ψ K).p=(param):=(course.1.walk K (floor.trans ub) cut).truep.point
  have gate:(R.family.path.rep N per K).p=(Ψ K).p:=(R.makes.wilson.represents N per K cut).vac.trans point.symm
  have cold:∀U,(∀a∈X,Healthy (Ψ K).p.threshold (halo (Ψ K).p.B {a}) U)→‖Y U‖≤0:=by
    intro U clear
    have off:U∉E:=by
      rintro ⟨z,hz,bad⟩
      rw [gate] at bad
      exact Finset.disjoint_left.mp (clear z hz) (halo_subset _ _ (mem_singleton_self z)) bad
    simp [Y,off]
  letI:IsProbabilityMeasure (scene R.family.path N per K):=probability R.makes.wilson cut
  have integrable:Integrable Y (scene R.family.path N per K):=(integrable_const _).indicator hm
  have flat:=WilsonOriginalMicroscopicUpperFlatHalos.original R π Γ Ψ course cut top (R.family.localSection 0)
    R.family.params simple way D Q ticket floor ub fixed cap X id Y borel (e:=0) (M:=1) le_rfl zero_le_one
    (fun U=>by by_cases h:U∈E <;> simp [Y,h]) cold ui before
  rw [WilsonOriginalFailedHaloPosterior.flat R before cut Y integrable] at flat
  have paid:(μ before (1:Config G (R.family.side i per))).real E ≤
      (X.card:ℝ)*(4*hitWidth (param)*Real.exp ((param).supportExponent+2)*H*R.alloy.B.a.clock.forcedAllowance K):=by
    simpa only [Y,integral_indicator_const _ hm,Complex.real_smul,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg measureReal_nonneg,one_mul,zero_add,housed] using flat
  obtain ⟨restricted,rare⟩:=(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple p positive)).choose_spec K late
  have beta:0≤H:=zero_le_one.trans (R.alloy.B.a.fits.delayed K).le
  apply (WilsonOriginalDecoderPosterior.original R before cut V hm).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply paid.trans
  calc
    _=((X.card:ℝ)*(4*Real.exp ((param).supportExponent+2)))*(H*(hitWidth (param)*R.alloy.B.a.clock.forcedAllowance K)):=by ring
    _≤_:=mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left restricted beta).trans rare) (by positivity)

end YM.Integration.WilsonOriginalMicroscopicEntranceHeldHalo
end
