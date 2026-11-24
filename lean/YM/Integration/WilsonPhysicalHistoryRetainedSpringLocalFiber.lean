import YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalTilt
import YM.Integration.WilsonHeldRetainedAction

/-! The true conditioned Haar step at any held coarse field and any fixed
fine exterior, with the complete earlier signed expenditure on each side. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Finset Lattice RG Wilson MeasureTheory
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic RG01Estimate
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato OPE.Therm WilsonCoeffUV.Bank.Ticket
open OriginalMarkedRowCovariance WilsonHeldRetainedAction OriginalMarkedConditionalAction
open Pert.Asymptotics AnalyticBridge VerifiedReset Collection Quotes
open scoped Classical BigOperators Topology
variable {G:Gauge}

theorem score_meas (R:Run G)(N per j r:ℕ)(live:j≤N)(Z:SeriesA G)(σ C:ℝ)
    (A:Listing G (R.family.side j per))(t:ℕ)
    (cash:Meadow.Budget (R.family.path.rep N per j).p
      (maskedSpringModel R N per j r Z σ C A t).listing.reg (maskedSpringModel R N per j r Z σ C A t).trunk
      (maskedSpringModel R N per j r Z σ C A t).bill)
    (filed:∀U,let P:=R.family.path.rep N per j
      let M:=maskedSpringModel R N per j r Z σ C A t
      HasSum (fun i=>masked P.p.threshold (M.listing.reg i).support (M.trunk i) U)
        (∑x,maskedSpringAt R N per j r Z σ C (regulatorRun R.family N per j) x U)):
    Measurable (maskedSpringScore R N per j r Z σ C):=by
  let P:=R.family.path.rep N per j
  let M:=maskedSpringModel R N per j r Z σ C A t
  obtain ⟨b,_,paid⟩:=cash
  have rows (i:ℕ):Measurable (masked P.p.threshold (M.listing.reg i).support (M.trunk i)):=
    masked_measurable _ _ _ (paid i).1.borel
  have same:(fun U=>∑x,maskedSpringAt R N per j r Z σ C (regulatorRun R.family N per j) x U)=
    fun U=>∑'i,masked P.p.threshold (M.listing.reg i).support (M.trunk i) U:=
    funext fun U=>(filed U).tsum_eq.symm
  apply (Activities.E_measurable (R.makes.wilson.represents N per j live).good.labels.regular).sub
  rw [same]
  exact Measurable.tsum rows

theorem cofinal_spring_fiber (R:Run G)(simple:G.Simple)
    (render:WilsonVacuumPreResetRenderCalendar.Issued R.kit)
    (curves:WilsonVacuumPreResetPrecursorReserve.Issued R.kit):
    let V:=R.family.path.levels
    ∀ᶠm:ℕ in atTop,let j:=m+1
      ∀N,j<N→∀per (A:Listing G (R.family.side j per)),∀σ C:ℝ,0<σ→σ⁻¹≤zz V j→
      ∀Z:SeriesA G,Draw Z σ C→∀r:ℕ,∀ᶠt:ℕ in atTop,
      let P:=R.family.path.rep N per j
      let M:=maskedSpringModel R N per j r Z σ C A t
      ∀(S:Support (R.family.side j per))(exterior:Config G (R.family.side j per)) (W:Config G (R.family.side m per)),let ξ:=OriginalMarkedConditionalAction.patch S exterior
      let μ:=reference R N per m S exterior W
      let a:=OriginalMarkedLocalPurchase.fee V j S (V.clock.allowance j+M.bill)
      ∀F:Config G (R.family.side j per)→ℂ,Measurable F→∀B:ℝ,0≤B→(∀u,‖F u‖≤B)→
        ‖read μ (fun u=>maskedSpringWeight R (N:=N) r Z σ C (ξ u)) (fun u=>F (ξ u))-
          reading R N per m S exterior W P F‖≤2*Real.exp (2*a)*a*B:=by
  intro V
  filter_upwards [cofinal_spring_change R simple render curves,
    cofinal_mask_source R simple render curves] with m earned actual
  intro j N live per A σ C hs fund Z draw r
  filter_upwards [earned N live per A σ C hs fund Z draw r] with t price
  intro P M S exterior W ξ μ a F meas B pos cap
  letI:IsProbabilityMeasure μ:=probability R N per m S exterior W
  have data:=actual N live.le per A σ C hs fund Z draw r t P.p.B
  have measured:=score_meas R N per j r live.le Z σ C A t price.2.1 data
  have earlier (u):|maskedSpringScore R N per j r Z σ C (ξ u)-maskedSpringScore R N per j r Z σ C exterior|≤a:=
    price.2.2 S (ξ u) exterior (outside S exterior u)
  exact spring_fiber R live.le r Z σ C μ ξ (measurable_patch S exterior) exterior measured a earlier
    (fun u=>F (ξ u)) (meas.comp (measurable_patch S exterior)) B pos (fun u=>cap _)

end YM.Integration.OriginalMarkedRunAction
