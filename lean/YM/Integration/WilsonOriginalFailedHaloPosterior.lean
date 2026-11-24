import YM.Integration.WilsonReceivedQuietCrownFlat
import YM.Integration.WilsonSeparatedOriginalPosteriorTransport
import YM.Integration.WilsonMacroscopicRichFlatPosteriorLaw

/-! Price failures of the native retained halos at the actual earlier flat
field. Every owner uses the same normalized positive Wilson posterior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFailedHaloPosterior
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner OPE.Therm
open scoped BigOperators Classical

theorem flat {G:Gauge}(R:Run G){N per b i:ℕ}(ib:i+1 ≤ b)(live:b ≤ N)
    (X:Config G (R.family.side b per)→ℂ)(bill:Integrable X (scene R.family.path N per b)):
    actualTransport R.family (N:=N) X ((Nat.le_succ i).trans ib) 1 =
      ∫U,X U ∂WilsonMacroscopicRichFlatPosteriorLaw.law R N per ib 1:=by
  calc
    _=WilsonMacroscopicForwardTransfer.exterior (C:=R.family) (N:=N) ((Nat.le_succ i).trans ib) X 1:=
      congrFun (WilsonSeparatedOriginalPosteriorTransport.realized (C:=R.family) (N:=N) (p:=per) R.makes live
        ((Nat.le_succ i).trans ib) X bill).symm 1
    _=_:=WilsonMacroscopicRichFlatPosteriorLaw.reading R ib live 1 X bill

variable {G:Gauge}(R:Run G){N per m k b:ℕ}(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)
   (Ψ:∀j,RG.Rep G (R.family.side j per))(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
   (top:b ≤ N){d:ℕ}{F:Frame G d}(S:SectionData F)(A:Hol G)
   (simple:G.Simple)(way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
   (Q:D.Tab R.rolls)(ticket:TicketP R.alloy R.kit D Q){u:ℕ}(floor:m ≤ u)(ub:u ≤ b)
   (fixed:WilsonSingleHardRadius.first R simple ≤ u)
local notation "κ" => LocalComparison.forcedDivisor R.family b
local notation "β" => R.alloy.B.a.clock.hatBeta b
local notation "Space" => Config G (R.family.side b per)

include course top way ticket floor ub fixed S A in
theorem one (event:Set Space)(meas:MeasurableSet event)(y:Site (R.family.side b per))
    {cash:ℝ}(pos:0<cash)
    (owner:Owned (F:=F) (Ψ b) A y κ cash (fun U=>((Ψ b).eval U:ℂ)*
      event.indicator (fun _=> (1:ℂ)) U)){i:ℕ}(ui:u ≤ i)(ib:i+1 ≤ b):
    (WilsonMacroscopicRichFlatPosteriorLaw.law R N per ib 1).real event ≤ 4*cash*β*κ:=by
  obtain ⟨q,fit,due,hit⟩:=owner
  let μ:=WilsonMacroscopicRichFlatPosteriorLaw.law R N per ib 1
  let X:Space→ℂ:=event.indicator (fun _=>(1:ℂ))
  letI:IsProbabilityMeasure (scene R.family.path N per b):=probability R.makes.wilson top
  have bill:Integrable X (scene R.family.path N per b):=(integrable_const (1:ℂ)).indicator meas
  have pay:=WilsonMeasuredOwnerFlatCourse.original R π Γ Ψ course top S A y q fit due simple way D Q ticket
    floor ub fixed pos (le_refl cash) ui ((Nat.le_succ i).trans ib)
  have same:(Ψ b).eval=(R.family.path.rep N per b).eval:=(course.1.walk b (floor.trans ub) top).view
  have source:(fun U=>((Ψ b).eval U)⁻¹ • account q (Ψ b) U)=X:=by
    funext U
    have hp:0<(Ψ b).eval U:=by rw [same];exact Multi.AxisShift.chosen_positive R.makes.wilson top U
    rw [hit,Complex.real_smul,Complex.ofReal_inv,←mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hp.ne'),one_mul]
  rw [source,flat R ib top X bill] at pay
  change ‖∫U,X U ∂μ‖ ≤ _ at pay
  simpa only [X,integral_indicator_const _ meas,Complex.real_smul,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg measureReal_nonneg] using pay

/-- A finite union on a single probability law. Each summand is the
positive price of a whole original event. -/
theorem envelope {X:Type*}[MeasurableSpace X](μ:Measure X)[IsProbabilityMeasure μ]
    {ι:Type*}[DecidableEq ι](roster:Finset ι)(E:ι→Set X)(meas:∀a∈roster,MeasurableSet (E a))
    (fee:ι→ℝ)(owner:∀a∈roster,μ.real (E a) ≤ fee a)(Y:X→ℂ)(borel:Measurable Y)
    {e M:ℝ}(ep:0 ≤ e)(mp:0 ≤ M)(gross:∀U,‖Y U‖ ≤ M)
    (clear:∀U,(∀a∈roster,U∉E a)→‖Y U‖ ≤ e):
    ‖∫U,Y U ∂μ‖ ≤ e+M*∑a∈roster,fee a:=by
  let hit (a:ι):X→ℝ := (E a).indicator (fun _=>1)
  have nz (a:ι)(U:X):0 ≤ hit a U:=Set.indicator_nonneg (fun _ _=>zero_le_one) _
  have hi:Integrable Y μ:=Integrable.of_bound borel.aestronglyMeasurable M (ae_of_all _ gross)
  have ri (a:ι)(mem:a∈roster):Integrable (hit a) μ:=(integrable_const _).indicator (meas a mem)
  have sumInt:Integrable (fun U=>∑a∈roster,hit a U) μ:=integrable_finsetSum _ ri
  have bound (U:X):‖Y U‖ ≤ e+M*∑a∈roster,hit a U:=by
    by_cases here:∀a∈roster,U∉E a
    · exact (clear U here).trans (le_add_of_nonneg_right (mul_nonneg mp (sum_nonneg (fun a _=>nz a U))))
    push Not at here
    obtain ⟨a,mem,yes⟩:=here
    have base:1 ≤ ∑b∈roster,hit b U:=by
      calc 1=hit a U:=by simp [hit,yes]
           _ ≤ _:=Finset.single_le_sum (fun b _=>nz b U) mem
    exact (gross U).trans ((le_mul_of_one_le_right mp base).trans (le_add_of_nonneg_left ep))
  calc
    _ ≤ ∫U,‖Y U‖ ∂μ:=norm_integral_le_integral_norm _
    _ ≤ ∫U,e+M*∑a∈roster,hit a U ∂μ:=integral_mono hi.norm ((integrable_const _).add (sumInt.const_mul _)) bound
    _=e+M*∑a∈roster,μ.real (E a):=by
      rw [integral_add (integrable_const _) (sumInt.const_mul _),integral_const_mul,integral_finsetSum _ ri]
      simp only [integral_const,probReal_univ,one_smul]
      congr 2
      apply Finset.sum_congr rfl
      intro a mem
      simpa [hit] using (integral_indicator_const (μ:=μ) (1:ℝ) (meas a mem))
    _ ≤ _:=add_le_add_right (mul_le_mul_of_nonneg_left (Finset.sum_le_sum owner) mp) _

include course top way ticket floor ub fixed S A in
theorem original {ι:Type*}[DecidableEq ι](seats:Finset ι)(E:ι→Set Space)(meas:∀a∈seats,MeasurableSet (E a))
    (y:ι→Site (R.family.side b per))(cash:ι→ℝ)(pos:∀a∈seats,0<cash a)
    (owners:∀a∈seats,Owned (F:=F) (Ψ b) A (y a) κ (cash a) (fun U=>((Ψ b).eval U:ℂ)*
      (E a).indicator (fun _=> (1:ℂ)) U))(Y:Space→ℂ)(borel:Measurable Y){e M:ℝ}
    (ep:0 ≤ e)(mp:0 ≤ M)(gross:∀U,‖Y U‖ ≤ M)(clear:∀U,(∀a∈seats,U∉E a)→‖Y U‖ ≤ e)
    {i:ℕ}(ui:u ≤ i)(ib:i+1 ≤ b):
    actualTransport R.family (N:=N) Y ((Nat.le_succ i).trans ib) 1 ∈
      Metric.closedBall 0 (e+M*∑a∈seats,4*cash a*β*κ):=by
  let μ:=WilsonMacroscopicRichFlatPosteriorLaw.law R N per ib 1
  letI:IsProbabilityMeasure μ:=WilsonMacroscopicRichFlatPosteriorLaw.prob R ib top 1
  letI:IsProbabilityMeasure (scene R.family.path N per b):=probability R.makes.wilson top
  have bill:Integrable Y (scene R.family.path N per b):=Integrable.of_bound borel.aestronglyMeasurable M (ae_of_all _ gross)
  rw [Metric.mem_closedBall,dist_zero_right,flat R ib top Y bill]
  exact envelope μ seats E meas _ (fun a mem=>one R π Γ Ψ course top S A simple way D Q ticket floor ub fixed
    (E a) (meas a mem) (y a) (pos a mem) (owners a mem) ui ib) Y borel ep mp gross clear

end YM.Integration.WilsonOriginalFailedHaloPosterior
end
