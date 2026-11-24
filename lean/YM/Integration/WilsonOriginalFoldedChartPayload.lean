import YM.Integration.WilsonOriginalRegisteredFoldedQ

/-! The independently folded original source and its normalizer under the actual change of the Gaussian coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFoldedChartPayload
open Function Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay WilsonVacuumPreResetDepositedGeometric
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonOriginalRelativeFoldedQuiet (relative)
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {G:Gauge}(R:Run G)(N i p:ℕ)(hi:i<N)(F:Forest (step R i p).ratio)(tag:(step R i p).Choices)
local notation "P" => covered R N i p
local notation "K" => model R N i p hi
local notation "C₁" => Woods G (coarse R i p)

private theorem trim {T:Type*}[CommRing T](a:PowerSeries T) :
    constantCoeff (a-PowerSeries.C (constantCoeff a))=0:=by simp

include tag in
private theorem phase_aux (prior:PChart G (fine R i p))(shell:shellK 2 prior)
    (head:prior 0=shine (orbQ (precisionC G (fine R i p) (upper R N i)))) :
    WilsonOriginalRelativeFoldedQuiet.relative R N i p hi F prior=relativePhase R N i p hi F prior 0 :=by
  apply PowerSeries.ext
  intro d
  by_cases hd:d=0
  · subst d
    rw [coeff_zero_eq_constantCoeff_apply,coeff_zero_eq_constantCoeff_apply,
      phase_zero R N i p hi F tag prior shell head 0 (map_zero _)]
    exact trim _
  · unfold WilsonOriginalRelativeFoldedQuiet.relative relativePhase
    rw [map_sub (retool _),retool_tall,map_zero,add_zero]
    simp [map_add,map_sub,holdUp,orbC,body_orb_C,coeff_C,hd]

include tag in
theorem phase (simple:G.Simple) :
    WilsonOriginalRelativeFoldedQuiet.relative R N i p hi F P=relativePhase R N i p hi F P 0 :=by
  have price:=WilsonVacuumPreResetTorusUpperQuadratic.original R simple N (i+1) hi (fine R i p)
  exact phase_aux R N i p hi F tag P price.1 price.2

/-- Both the marked numerator and its complete unmarked denominator use the same upper action, original forest and actual covariance. -/
theorem original (simple:G.Simple)(w:Ink (Active G F⊕Woods G (coarse R i p))):
    let φ:=relative R N i p hi F P
    let ψ:=shot (step R i p) F (prediction R N i p) (ratio R) P
    let Q:=(K).covariance F tag
    Wick (C₁) Q (raiseE ψ*w) =
        Wick (C₁) Q (raiseE φ*retool (shift R N i p hi F) w) ∧
      inside (step R i p) F (upper R N i) (prediction R N i p) (ratio R) P =
        Wick (C₁) Q (raiseE φ) :=by
  intro φ ψ Q
  have price:=WilsonVacuumPreResetTorusUpperQuadratic.original R simple N (i+1) hi (fine R i p)
  have h:=insertion R N i p hi F tag P price.1 price.2 0 (map_zero _) w
  have hz:=WilsonVacuumPreResetStationaryChange.original R N i p hi F tag simple 0 (map_zero _)
  rw [←phase R N i p hi F tag simple] at h
  simp only [raise_still,one_mul] at h
  refine ⟨h,?_⟩
  simpa only [relativeMass,←phase R N i p hi F tag simple,raise_still,one_mul] using hz

end YM.Integration.WilsonOriginalFoldedChartPayload
