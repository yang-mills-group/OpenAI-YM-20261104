import YM.Integration.WilsonVacuumPreResetDepositedLetters

/-! On a correctly filed original inlet, stripping the leading
Gaussian quadratic gives the actual Haar/Schur relative phase. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetDepositedPhase
open Function Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay WilsonVacuumPreResetDepositedLetters
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {G:Gauge}(R:Run G)(N m p:ℕ)(hm:m<N)(F:Forest (step R m p).ratio)
variable (tag:(step R m p).Choices)(Z:SeriesA G)

include hm in
theorem head (simple:G.Simple)(row:∀j, filed R N m p Z 0 (j+1)=
    emera (actionW (levels R) (ratio R) N (m+1)) (fine R m p) 0 (j+1)):
    filed R N m p Z 0=shine (orbQ (precisionC G (fine R m p) (upper R N m))):=by
  have top:=(WilsonVacuumPreResetTorusUpperQuadratic.original R simple N (m+1) hm (fine R m p)).2
  funext j
  cases j with
  | zero=>
    change front (income R N m p).path (income R N m p).clip (fine R m p) 0 0+
      sands Z (fine R m p) 0 0=_
    have entry:=front_full (R.makes.wilson.represents N p (m+1) hm).good.paths (fine R m p)
    change front (income R N m p).path (income R N m p).clip (fine R m p)=_ at entry
    rw [entry]
    simp only [Pi.add_apply,Pi.smul_apply,sprig,sands_zero_v,add_zero,
      shine_dark (k:=2) (n:=0) (by decide),smul_zero]
  | succ j=>exact (row j).trans (congrFun top _)

include tag in
theorem phase (head: filed R N m p Z 0=shine (orbQ (precisionC G (fine R m p) (upper R N m)))):
    opened R N m p hm F Z=relativePhase R N m p hm F (filed R N m p Z) 0:=by
  have shell:shellK 2 (filed R N m p Z):=WilsonLimitConstruction.FundedSpringPeriodGerm.grade _ _ _ _
  apply PowerSeries.ext
  intro j
  by_cases hj:j=0
  · subst j
    rw [coeff_zero_eq_constantCoeff_apply,coeff_zero_eq_constantCoeff_apply,
      WilsonVacuumPreResetDepositedLetters.leading,phase_zero R N m p hm F tag _ shell head 0 (map_zero _)]
  · unfold WilsonVacuumPreResetDepositedLetters.opened exponent relativePhase
    rw [map_sub (retool _),retool_tall,map_zero,add_zero]
    simp [map_add,map_sub,holdUp,orbC,body_orb_C,coeff_C,hj]

end YM.Integration.WilsonVacuumPreResetDepositedPhase
