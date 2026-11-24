import YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogPhysical

/-! Before the first physical cutoff, the full normalized logarithmic comparison of the
nominated initial marked Q with its independent compensated Wilson Taylor computation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogOriginal
open Filter Function Finset Lattice Wilson RG Precision Tree Marker Multi Exterior
open FullQLocal FullQLocal.RenderedStep LocalComparison LocalComparison.Global PhysicalNext.Repeat.Legato
open Comparison.RG02 Comparison.RG02.Order Pert.Asymptotics WilsonLimitConstruction
open WilsonMatrixTicketLanesReportedPrepaid
open scoped Classical BigOperators Topology
variable {G:Gauge} {B:MS.Local.Physical.Deck G} {V:Type} [DecidableEq V] [Fintype V] [Nonempty V]
local notation "Γ" => Stock.census V

theorem original (R:Run G) (hG:G.Simple) (paid:Paid G R.kit) (u:V→MS.Rake.Label B)
    (Q:MS.Land.Prescription B) (cap K₀ q:ℕ) (μ:ℝ) {ε:ℝ} (ep:0<ε):
    ∃n ≥ q,∀ᶠ b:ℕ in atTop,∀(J:Request V)(A:NumericSchedule R.family J)
      (profile:∀k,k ≤ (R.metals.p.profile k).order ∧ k ≤ (R.metals.p.profile k).power)
      (d:LocalFormal.Datum R.family (Γ)),d.level=b→d.cutoff=d.level+1→
      ∀(o:V→Site (R.family.side (d.level+1) d.period)) (ks:V→ℕ),(∀i,ks i ≤ K₀)→
      ∀(hm:ActualOriginalQInitialInput.start R hG u J A profile ≤ d.level)
        (hp:(ActualOriginalQPointSetup.request R u J).physicalPeriodLower ≤ (R.family.S.period d.period).val),
      ActualOriginalQLayout.referenceLevel R u ≤ d.level+1→
      ∀(t:TestSpace (ActualOriginalQPointSetup.request R u J).tests),
        let W:=FundedMatchedPointOpening.colors R hG u J A d Q o μ ks profile hm hp t
        let K:=d.kernel (RunFormalChain.fromRun R)
        let Kₙ:=(RunFormalChain.fromRun R).step (d.level+1) d.level d.period (Nat.lt_succ_self _)
        let g:=regulatorRun R.family d.cutoff d.period (d.level+1)
        let gₙ:=regulatorRun R.family (d.level+1) d.period (d.level+1)
        let S:=R.family.path.levels.clock.op d.level d.period
        let P:=R.family.path.rep d.cutoff d.period (d.level+1)
        let X:=((ActualOriginalQInitialPreparation.input R hG u J A d Q o μ ks).leaf t).density
        let w:=WilsonPositionSeparatedProfileMayerInitialLogWeights.weight
          (WilsonPositionSeparatedProfileMayerInitialThermalWords.reader R hG u J A d Q o μ ks t)
        ∀(F:Forest S.ratio)(tag:S.Choices)(a:fieldDir G (R.family.side d.level d.period) 1),
          (∀i,‖Exterior.collect G a i‖ ≤ (cap:ℝ)+1)→
          let Z:=fun _:S.Choices=>Integral.zone K P.p F g a
          let diff:=Local.cumulant P X S (Integral.sample gₙ a)-
            Order.value (gₙ:ℂ) (Order.logMarked (Bulk.Fk Kₙ F tag W a n))
          (Local.markingError P X K g F tag W Z a n (Fintype.card V)=diff) ∧
          Poly.price w diff ≤ ε*gₙ^q ∧
          Poly.price w (Local.markingError P X K g F tag W Z a n (Fintype.card V)) ≤ ε*gₙ^q:=by
  classical
  obtain ⟨E,C,cp,book⟩:=WilsonPositionSeparatedProfileMayerInitialLogCohort.purchased R hG paid Q u K₀ cap μ
  obtain ⟨n,reserve,degree,dates⟩:=book q
  let money:=WilsonPositionSeparatedProfileMayerInitialLogPhysical.amount (L:=V) n C
  have mp:0 ≤ money:=by dsimp [money,WilsonPositionSeparatedProfileMayerInitialLogPhysical.amount];positivity
  have plus:0<1+money:=by linarith
  obtain ⟨b₀,small⟩:=eventually_atTop.1 (IterationFour.Currency.g_small hG R.makes
    (min 1 (ε/(1+money))) (lt_min zero_lt_one (div_pos ep plus)))
  refine ⟨n,(Nat.le_add_right q _).trans reserve,?_⟩
  filter_upwards [dates,eventually_ge_atTop b₀] with b sale late
  intro J A profile d hb top o ks limits hm hp ref t W K Kₙ g gₙ S P X w F tag a inside Z diff
  subst b
  have gp:0<gₙ:=IterationFour.Currency.g_pos R.makes _ _ _ le_rfl
  have shrunk:gₙ < min 1 (ε/(1+money)):=small (d.level+1) (by omega) (d.level+1) d.period le_rfl
  have g₁:gₙ ≤ 1:=shrunk.le.trans (min_le_left _ _)
  have cash:gₙ*(1+money) ≤ ε:=(le_div_iff₀ plus).mp (shrunk.le.trans (min_le_right _ _))
  have take:gₙ^(q+1)*money ≤ ε*gₙ^q:=by
    calc
      _=gₙ^q*(gₙ*money):=by ring
      _ ≤ gₙ^q*ε:=mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg gp.le _)
      _=_:=mul_comm _ _
  have scored:=WilsonPositionSeparatedProfileMayerInitialLogPhysical.priced R hG u J A d Q o μ ks
    profile hm hp paid top ref t F tag a cap K₀ q E n C cp.le reserve g₁ limits inside degree sale
  have exactAmount:=WilsonPositionSeparatedProfileMayerInitialLogPhysical.error R hG u J A d Q o μ ks
    profile hm hp top ref t F tag a n
  refine ⟨exactAmount,scored.trans take,?_⟩
  rw [exactAmount]
  exact scored.trans take

end YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogOriginal
