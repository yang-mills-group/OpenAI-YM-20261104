import YM.Integration.WilsonVacuumPreResetDepositedPhase
import YM.Integration.WilsonVacuumPreResetDepositedMass
import YM.Integration.WilsonLimitConstruction.FundedSpringWickExponential

/-! The original finite-period vacuum logarithm in absolute links.
The same common stationary change transports its density and determinant. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetDepositedAction
open Function Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Mosaic WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay
open WilsonVacuumPreResetDepositedGeometric WilsonVacuumPreResetDepositedMass
open Marker Multi Order Cumulants WilsonVacuumPreResetFiniteRegister
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner

variable {G:Gauge}(R:Run G)(N m p:ℕ)(hm:m<N)(F:Forest (step R m p).ratio)
variable (tag:(step R m p).Choices)(Z:SeriesA G)
variable (head:filed R N m p Z 0=shine (orbQ (precisionC G (fine R m p) (upper R N m))))

abbrev originalMass := inside (step R m p) F (upper R N m) (prediction R N m p) (ratio R) (filed R N m p Z)

include head in
theorem stationary:mass R N m p hm F tag Z=originalMass R N m p F Z:=by
  have shell:shellK 2 (filed R N m p Z):=WilsonLimitConstruction.FundedSpringPeriodGerm.grade _ _ _ _
  have e:=WilsonVacuumPreResetStationaryChange.empty R N m p hm F tag _ shell head 0 (map_zero _)
  rw [raise_still,one_mul] at e
  change mass R N m p hm F tag Z=inside _ _ _ _ _ _
  rw [e,WilsonVacuumPreResetDepositedMass.mass,WilsonVacuumPreResetDepositedPhase.phase R N m p hm F tag Z head]

private theorem opening {I Y:Type}[Fintype I][Fintype Y](q:Matrix I I ℝ)(P:Ink (I⊕Y))
    (h:constantCoeff P=0):constantCoeff (Wick Y q (raiseE P))=1:=by
  have hp:coeff 0 (raiseE P)=coeff 0 (1:Ink (I⊕Y)):=by
    simp [coeff_zero_eq_constantCoeff_apply,raise_one h]
  calc
    _=constantCoeff (Wick Y q 1):=by
      rw [←coeff_zero_eq_constantCoeff_apply,←coeff_zero_eq_constantCoeff_apply]
      simp only [Wick,projectZero,coeff_map,fullB,blur,overlay_apply,hp]
    _=1:=by rw [W_one,map_one]

include hm tag head in
theorem unit:constantCoeff (originalMass R N m p F Z)=1:=by
  rw [←stationary R N m p hm F tag Z head]
  exact opening _ _ (WilsonVacuumPreResetDepositedLetters.leading R N m p hm F Z)

variable {T:Type}[DecidableEq T][Fintype T]{J:Census T}(Q:Bulk.Colors J G (fine R m p))
variable (cash:BudgetPoint)(cap:ℕ){σ C:ℝ}(width:0<σ)(draw:Draw Z σ C)
    (low:∀a∈Z,3≤a.grade)(high:∀a∈Z,a.grade≤cap)
    (x:fieldDir G (coarse R m p) 1)(r:ℕ)

include head cash width draw low high in
theorem original:
    logVac (Bulk.Fk (model R N m p hm) F tag (source R m p Z Q cap) x r)=
      register J r (OriginalRadialSeries.observed (flatten x) (logOf (originalMass R N m p F Z))):=by
  let Q₀:=Bulk.Colors.noHole G (fine R m p) J
  calc
    _=logVac (Bulk.Fk (model R N m p hm) F tag (source R m p Z Q₀ cap) x r):=by
      unfold logVac
      exact congrArg Extra.Trajectories.connected
        (Symmetry.Pole.carry (W:=source R m p Z Q cap) (W':=source R m p Z Q₀ cap) (model R N m p hm) F tag x r rfl)
    _=_:=by
      rw [WilsonVacuumPreResetDepositedMass.normalized R N m p hm F tag Z Q₀ cash cap width draw low high x r
        (Bulk.Colors.no_hole G (fine R m p) J).1,stationary R N m p hm F tag Z head]
      exact congrArg (register J r) (WilsonLimitConstruction.FundedSpringWickExponential.log_map
        (fun v:Woods G (coarse R m p)→ℝ=>MvPolynomial.eval v) _ (unit R N m p hm F tag Z head) (flatten x)).symm

include head cash width draw low high in
theorem read (t:ℕ)(ht:t≤r):
    Laplace.detail (logVac (Bulk.Fk (model R N m p hm) F tag (source R m p Z Q cap) x r)) J.quiet t=
      (MvPolynomial.eval (flatten x) (coeff t (logOf (originalMass R N m p F Z))):ℝ):=by
  rw [original R N m p hm F tag Z head Q cash cap width draw low high x r]
  unfold Laplace.detail register
  rw [RingHom.comp_apply,observation J r _ ht,coeff_map,RingHom.comp_apply,Assembly.beads,if_pos rfl]
  rfl

end YM.Integration.WilsonVacuumPreResetDepositedAction
