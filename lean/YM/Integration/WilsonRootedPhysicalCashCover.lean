import YM.Integration.WilsonVacuumPreResetCatalogue
import YM.Integration.WilsonOriginalHighSelection
import YM.Push.GRID_APPROXIMATION.Hit

/-! The real old Cash rows at one unit beyond the regular headline, at their
original common physical station and before any period or forest is selected. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedPhysicalCashCover
open Function Filter Finset Lattice Wilson RG RG.Shoot Pressure
open Push Push.AbsoluteSums Push.AbsoluteSums.Animals Gas Ursell Trees Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes PhysicalNext PhysicalNext.Repeat Legato
open ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.Blaze Blaze.March Captain
open Opera Height Beam Song Greenbelt Next.Scheduling Extra.Iteration UVNext
open PriceCompiler Org Input Supply Pressure.Testing Time Roost Match Refrain
open RG01Estimate RG01Estimate.CensusStep WilsonLimitConstruction.FundedCensusVacuum
open scoped Topology BigOperators Classical

variable {G : Gauge} (R : Run G) {m N per : ℕ} (S : Station R N per m)
local notation "H" => S.guide
local notation "B" => R.alloy.B.a.budget m
local notation "α" => R.alloy.B.kin.alpha N m
local notation "J" => R.alloy.B.a.clock.J
local notation "θ" => R.alloy.B.a.clock.hatBeta

private def raised (p : BudgetPoint) : BudgetPoint :=
  {p with supportExponent:=p.supportExponent+1,exponent_pos:=by linarith only [p.exponent_pos]}

/-- The original pre-period salary buys the complete retained rows and their original derivative
norms at sigma plus four, per physical root and without a full-period factor. -/
theorem original (salary : WilsonOriginalHighSelection.Salary G R.kit) (hm : m<N) (r : ℕ) :
    ∃ f : (H).fragrances→ℝ,
      (∀ i,(B).supBounds (dashboard H i).site (dashboard H i).support
        (Height.lower H S.identity Chi.canonical (lit R.kit H H S.identity r) α (.inl i)) (f i)) ∧
      Footprint.Anchored (fun i=>(dashboard H i).site) f
        (fun i=>coverNumber (B).B (dashboard H i).support) (preExponent B+1)
        ((θ (m+1))^((R.kit.expense (J (m+1)) (J m)).wanting)) := by
  let x:=θ m
  let c:=J m
  let j:=J (m+1)
  let K:=R.metals.p.profile c
  have step : StepStages j c:=step_paid R.alloy.B.a m
  have paid:=R.alloy.B.valid.pays m
  have heights:=R.kit.pledging.jewels j x paid c step
  let T:=ships R.alloy.B N m per
  obtain ⟨Y',d',v,t',Av,b',r',B',q',i',z,⟨cap,g⟩,admit,price⟩:=
    heights.2 _ _ _ T (H).laws.data.funds (protocol R.alloy.B hm R.kit.pledging.conducts.full) _ H
  have hr : R.alloy.B.a.params m=K:=params_eq R.alloy.B.valid m
  have hp : (B).power=K.power:=congr_arg RG.Stage.power hr
  have hj : (B).order=K.order:=congr_arg RG.Stage.order hr
  have strong : preExponent (raised B)≤(R.kit.expense j c).earn := by
    rw [salary j c]
    change (R.alloy.B.a.params m).supportExponent+1+3≤1000*(10+(R.metals.p.profile j).supportExponent)+
      (R.metals.p.profile c).supportExponent+4
    rw [hr]
    linarith only [(R.metals.p.profile j).price_pos]
  have sup (i : (H).fragrances) :=(VacuumListing.pocket_dash H B Chi.canonical S.identity cap rfl hj.le hp.le i).2
  have all:=admit.applies cap K.power 0
  simp only [Nat.zero_le,↓reduceIte,pow_zero,mul_one] at all
  let f (i : (H).fragrances):=if lit R.kit H H S.identity r i then 0 else cap.markΦ (S.identity.furrow i) K.power
  refine ⟨f,?_,?_⟩
  · intro i
    by_cases h : lit R.kit H H S.identity r i
    · simp only [Height.lower,Height.chosen,Sum.elim_inl,h,↓reduceIte,f]
      simpa only [abs_zero] using! (CouplingShape.sup_const (G:=G) (p:=B) (X:=(dashboard H i).support)
        (o:=(dashboard H i).site) 0)
    · simpa only [Height.lower,Height.chosen,Sum.elim_inl,if_neg h,f,Song.opus] using! sup i
  · have full:=VacuumListing.dash_hit H (raised B) S.identity rfl strong _ all
    intro x
    have e:=full x
    rw [PriceCompiler.beta_eq R.alloy.B.valid m]
    have start:=budget_loosen e price
    change SumBudget (fun i=>if (dashboard H i).site=x then f i*Real.exp ((preExponent B+1)*
      coverNumber (B).B (dashboard H i).support) else 0) _
    refine budget_mono start ?_ ?_
    · intro i
      split
      · apply mul_nonneg _ (Real.exp_pos _).le
        dsimp only [f];split
        · exact le_rfl
        · exact (sup i).1
      · exact le_rfl
    · intro i
      have same : preExponent B+1=preExponent (raised B):=by unfold raised preExponent;dsimp only;ring
      dsimp only [Function.comp_apply]
      split
      · rw [same]
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        dsimp only [f];split
        · exact (sup i).1
        · exact le_rfl
      · exact le_rfl

end YM.Integration.WilsonRootedPhysicalCashCover
