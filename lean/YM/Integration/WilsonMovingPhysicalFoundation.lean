import YM.Integration.WilsonMovingAtMenuRun
import YM.Integration.WilsonRootedPhysicalSpring
import YM.Integration.ManuscriptQLocalSpringTicket

/-! A single funded physical run pays the marked height on its actual numbered spring
and the independently requested OPE calendar, before source and test choices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingPhysicalFoundation
open Filter Lattice Wilson RG RG.Supply Precision Org Push.PriceCompiler
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Daisy.Charity.RG12 GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open FullQLocal FullQLocal.RenderedStep WilsonOriginalMarkedExistence
open scoped Classical Topology
universe u
variable {G : Gauge} {V : Type}

theorem purchased (ask : WilsonMovingShadowPrices.Ask) [Fintype V] (J : Request V) (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) (prediction : Prediction G)
    (price : WilsonMovingCommonPrices.AllPrices ask Real.log
      (@WilsonMovingStoredFactor.OnMenu G (@prediction))) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T), prediction R.kit ∧
      (∀ i, i ≤ (R.metals.p.profile i).order ∧ i ≤ (R.metals.p.profile i).power) ∧
      R2I.Funded ((Mallow.orbitD G).paired (garment10 G)) R T ∧
      Mallow.RG12.Earned (ManuscriptQLocalMarkedHeightRun.acquisition G J) R.kit.shape R.alloy.delay ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W := by
  obtain ⟨A, hp⟩ := FundedPlateauRun.purchaseAtMenu (ask := ask) (movable := WilsonOriginalLogLight.movable)
    hG ((Mallow.orbitD G).paired ((WilsonRootedJointCalendar.scheme G J).paired (garment10 G))) hε
    (fun s (_ : Precision.MapPrices) => NativeComponentRecipe.Choice s)
    (fun s _ => NativeComponentRecipe.available hG s) NativeComponentRecipe.floor NativeComponentRecipe.numeric
    ActualRunNativeComponentRecipe.postnumeric (@prediction) price
  have drop : R2I.Funded (garment10 G) A.run A.campaign :=
    { A.funded with localBudget := { A.funded.localBudget with
        tailor := fun j x hx i hi => (A.funded.localBudget.tailor j x hx i hi).2.2 } }
  have spring : R2I.Funded ((Mallow.orbitD G).paired (garment10 G)) A.run A.campaign :=
    { A.funded with localBudget := { A.funded.localBudget with
        tailor := fun j x hx i hi => ⟨(A.funded.localBudget.tailor j x hx i hi).1,
          (A.funded.localBudget.tailor j x hx i hi).2.2⟩ } }
  have height : Mallow.RG12.Earned (ManuscriptQLocalMarkedHeightRun.acquisition G J)
      A.run.kit.shape A.run.alloy.delay := fun j x hx i hi =>
    (A.funded.localBudget.tailor j x hx i hi).2.1.1
  exact ⟨A.run, A.campaign, A.pillars, hp, A.orders, spring, height, A.correlations hG,
    fundedOriginalRun_on.{u} hG A.pillars A.penalty drop
      (ActualRunNativeComponentRecipe.of_preselection A.run A.selected)
      A.orders A.treasury A.period A.readout⟩

end YM.Integration.WilsonMovingPhysicalFoundation
end
