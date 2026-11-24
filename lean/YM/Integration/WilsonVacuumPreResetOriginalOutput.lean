import YM.Integration.WilsonVacuumPreResetDepositedAction
import YM.Integration.WilsonVacuumPreResetDepositedInfrared
import YM.Integration.WilsonVacuumPreResetTorusFoldedOutput
import YM.Integration.WilsonVacuumPreResetTorusFoldedConditional

/-! The actual finite unmarked orbit reader on every forest is the
full signed pre-reset update on the folded cover inlet. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetOriginalOutput
open Function Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Mosaic WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay
open WilsonVacuumPreResetDepositedGeometric WilsonVacuumPreResetDepositedInfrared Marker Multi
open WilsonVacuumPreResetDepositedAction
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner

variable {G:Gauge}(R:Run G)(N m p:ℕ)(hm:m<N)(F:Forest (step R m p).ratio)
variable (tag:(step R m p).Choices)(Z:SeriesA G)
variable (head:filed R N m p Z 0=shine (orbQ (precisionC G (fine R m p) (upper R N m))))
variable {T:Type}[DecidableEq T][Fintype T]{J:Census T}(Q:Bulk.Colors J G (fine R m p))
variable (cash:BudgetPoint)(cap:ℕ){σ C:ℝ}(width:0<σ)(draw:Draw Z σ C)
    (low:∀a∈Z,3≤a.grade)(high:∀a∈Z,a.grade≤cap)

abbrev held (x:fieldDir G (coarse R m p) 1)(r t:ℕ):=
  Symmetry.Orbit.ground (model R N m p hm) F tag (source R m p Z Q cap) r t x

def diff {Y:Type}(P:Ink Y)(t:ℕ)(x y:Y→ℝ):ℝ:=
  MvPolynomial.eval x (coeff t P)-MvPolynomial.eval y (coeff t P)

abbrev covered := emera (actionW (levels R) (ratio R) N (m+1)) (fine R m p)
abbrev output := Blue.flash (coil0 (levels R) (ratio R) m N (coarse R m p))

include head cash width draw low high in
private theorem logged (x:fieldDir G (coarse R m p) 1)(r t:ℕ)(h:t≤r):
    Laplace.detail (Comparison.RG02.Order.logVac (Bulk.Fk (model R N m p hm) F tag
      (source R m p Z Q cap) x r)) J.quiet t=
      (MvPolynomial.eval (flatten x) (coeff t (logOf (originalMass R N m p (repeatF (step R m p)) Z))):ℝ):=by
  let Q₀:=Bulk.Colors.noHole G (fine R m p) J
  let K:=model R N m p hm
  let H:=repeatF (step R m p)
  let W:=source R m p Z Q cap
  let W₀:=source R m p Z Q₀ cap
  have proper:Bulk.Well W₀:=(QuadraticLocal.Fk.well _ _ (WilsonVacuumPreResetTorusDeposit.legal Z width draw low _) Q₀
    (Bulk.Colors.no_hole G (fine R m p) J).1).1
  have masks:Comparison.RG02.Order.logVac (Bulk.Fk K F tag W x r)=
      Comparison.RG02.Order.logVac (Bulk.Fk K F tag W₀ x r):=
    congrArg Extra.Trajectories.connected (Symmetry.Pole.carry (W:=W) (W':=W₀) K F tag x r rfl)
  have forests:= (Laplace.identical K F H tag 0 W₀ x cash r proper).2
  change Laplace.detail (Comparison.RG02.Order.logVac (Bulk.Fk K F tag W x r)) J.quiet t=_
  rw [masks,forests]
  exact WilsonVacuumPreResetDepositedAction.read R N m p hm H tag Z head Q₀ cash cap width draw low high x r t h

include head cash width draw low high in
theorem physical (x y:fieldDir G (coarse R m p) 1)(r t:ℕ)(h:t≤r):
    held R N m p hm F tag Z Q cap x r t-held R N m p hm F tag Z Q cap y r t=
      ((diff (logOf (originalMass R N m p (repeatF (step R m p)) Z)) t (flatten x) (flatten y)-
        diff (quadratic R N m p) t (flatten x) (flatten y)):ℝ):=by
  let K:=model R N m p hm
  let Q₀:=Bulk.Colors.noHole G (fine R m p) J
  have zero:
    (if t=0 then Symmetry.price K F tag x else 0)-(if t=0 then Symmetry.price K F tag y else 0)=
      -(diff (quadratic R N m p) t (flatten x) (flatten y):ℂ):=by
    by_cases hz:t=0
    · subst t
      rw [if_pos rfl,if_pos rfl]
      exact WilsonVacuumPreResetDepositedInfrared.original R N m p hm F tag Z head Q₀ cash cap
        width draw low high x y (Bulk.Colors.no_hole G (fine R m p) J).1
    · simp [hz,diff,WilsonVacuumPreResetDepositedInfrared.quadratic,orbC,coeff_C]
  unfold held Symmetry.Orbit.ground
  rw [logged R N m p hm F tag Z head Q cash cap width draw low high x r t h,
      logged R N m p hm F tag Z head Q cash cap width draw low high y r t h]
  push_cast [diff] at zero ⊢
  linear_combination zero

include head cash width draw low high in
theorem original (simple:G.Simple)(k:ℕ)
    (cells:∀t<k,coeff t (Blue.flash (filed R N m p Z)-Blue.flash (covered R N m p))=
        MvPolynomial.C (MvPolynomial.eval 0 (coeff t (Blue.flash (filed R N m p Z)-Blue.flash (covered R N m p)))))
    (x y:fieldDir G (coarse R m p) 1)(r t:ℕ)(read:t≤r)(file:t<k):
    held R N m p hm F tag Z Q cap x r t-held R N m p hm F tag Z Q cap y r t=
      -(diff (output R N m p) t (flatten x) (flatten y):ℂ):=by
  rw [physical R N m p hm F tag Z head Q cash cap width draw low high x y r t read]
  let S:=step R m p
  let A:=levels R
  let E:=emera (actionW A (ratio R) N (m+1)) (fine R m p)
  have hf:shellK 2 (filed R N m p Z):=WilsonLimitConstruction.FundedSpringPeriodGerm.grade _ _ _ _
  have hd:= (WilsonVacuumPreResetTorusUpperQuadratic.original R simple N (m+1) hm (fine R m p)).1
  have old:=WilsonVacuumPreResetTorusFoldedConditional.centered S (repeatF S) (upper R N m)
    (prediction R N m p) (ratio R) R.alloy.B.ratio (filed R N m p Z) E hf hd cells t file (flatten x) (flatten y)
  have present:=WilsonVacuumPreResetTorusFoldedOutput.original R simple N m p hm t (flatten x) (flatten y)
  change diff (logOf (originalMass R N m p (repeatF S) Z)) t _ _=diff (logOf (inside S (repeatF S) (upper R N m)
    (prediction R N m p) (ratio R) E)) t _ _ at old
  rw [old]
  exact_mod_cast present

end YM.Integration.WilsonVacuumPreResetOriginalOutput
