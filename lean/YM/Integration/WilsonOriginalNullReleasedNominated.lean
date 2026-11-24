import YM.Integration.WilsonOriginalNullReleasedStation
import YM.Integration.WilsonOriginalThermometerTopGrading
import YM.Integration.WilsonReportingAbsoluteInletSimultaneous

/-! The finite-column invoice for the original enrolled (6,4,4) cutoff functions. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullReleasedNominated
open Filter Function Finset Lattice RG Wilson Source Labels Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open Cells MeasureTheory Extraction Table Climb QuadraticLocal ConnectedActivityE6
open OPE.Therm Trace Trace.Pilot Next.UVStress Next.Rank Next.Rank.East MergeProof.East Next.Rank.Price
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG.Supply Precision Push.PriceCompiler
open WilsonOriginalStarSceneWords WilsonOriginalStarSceneRows WilsonOriginalStarSceneRent
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonPositionThermometerGradedReading
open WilsonOriginalThermometerPalette WilsonOriginalThermometerMicroscopic WilsonOriginalThermometerTopDensity
open private salary_cap from YM.Integration.WilsonOriginalThermometerTopGrading
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}
local notation "C₀"=>R.family
local notation "P"=>R.family.path.levels

theorem original (simple:G.Simple)(shop:WilsonReportingAbsoluteInletSimultaneous.StationInvoice R)
    (ε:ℝ)(ep:0<ε):
    ∀ᶠ k:ℕ in atTop,∀A:Group C₀ 6,A.station.k=k→A.station.checked f H A.horizon→close R A→
    ∀s N p:ℕ,k<N→k ≤ s→∀live:s ≤ N,∀W:Rep G ((C₀).side s p),W.p=(P).budget s→
    W.beta=((C₀).path.rep N p s).beta→∀j:Fin 3,∀home:Opened C₀ (levels j) s p,
      let v:=A.station.wheel.atCut (N,p) (index A (grade j)) (vector A univ j)
      let raw:=((C₀).factory (levels j) N p).terminal.symm v
      let M:=fitting (C:=C₀) (levels j) N p s R.makes home live
      let F:=(C₀).labels.level (levels j)
      F.coeffSize (F.scaled (Coat.gStep W.beta/W.p.threshold) (M raw))
        ≤ (2:ℝ)^(WilsonOriginalAdjacentMicroscopicPrice.height R (levels j)+1)*
          ((C₀).S.a k/(C₀).S.a s)^ε*(C₀).S.a k^(levels j)*((P).clock.hatBeta k)^ε*mass R:=by
  let demand:=fun (w:Sheet G)(_ : MapPrices)=>NativeComponentRecipe.Choice w
  have calendar:=WilsonPositionThermometerStationFunding.original demand NativeComponentRecipe.floor
    NativeComponentRecipe.numeric ActualRunNativeComponentRecipe.postnumeric R shop ε ep
  filter_upwards [calendar,WilsonOriginalThermometerPalette.station R (f:=f) (H:=H) simple ε ep,
    eventually_all.mpr (fun j:Fin 3=>eventually_ge_atTop ((C₀).ref (levels j)))] with k wages paid refs
  intro A date checked near s N p upper route live W tier beta j home v raw M F
  have awake₀:= (paid A date checked N p upper j).trans (mul_le_mul_of_nonneg_left (salary_cap R A near)
    (Real.rpow_nonneg (zero_le_one.trans ((P).fits.delayed k).le) _) )
  have price:=WilsonOriginalNullReleasedStation.original R (levels j) home (refs j) route live W tier beta v ε
    (fun i lo _=>wages i lo)
  calc
    _ ≤ (2:ℝ)^(WilsonOriginalAdjacentMicroscopicPrice.height R (levels j)+1)*
      ((C₀).S.a k/(C₀).S.a s)^ε*(C₀).S.a k^(levels j)*F.coeffSize (awake C₀ (levels j) k N p v):=price
    _ ≤ (2:ℝ)^(WilsonOriginalAdjacentMicroscopicPrice.height R (levels j)+1)*
      ((C₀).S.a k/(C₀).S.a s)^ε*(C₀).S.a k^(levels j)*(((P).clock.hatBeta k)^ε*mass R):=by
      apply mul_le_mul_of_nonneg_left awake₀
      have hk:= (C₀).S.a_pos k;have hs:=(C₀).S.a_pos s;positivity
    _ = _:=by ring
end YM.Integration.WilsonOriginalNullReleasedNominated
