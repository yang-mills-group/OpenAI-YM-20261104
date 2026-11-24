import YM.Integration.WilsonOlderFreshSoftSocketPole
import YM.Integration.SignedJointSourceMoments

/-! A single total pole clears every proper partition of an actual canonical finite socket planting. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketOpening
open Function Finset Lattice Wilson RG Source Labels Comparison.RG02
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Soil
open OriginalMarkedSourceComet IndependentSourcePathFamily WilsonThermometerDeclaredSeeds
open WilsonReceivedCanonicalVerseRegister (offer start)
open FormalBulk08 WilsonCoeffUV.Winding PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
open private dark from YM.Integration.IndependentSourcePathFamily
variable {G:Gauge}{I:Type}[DecidableEq I][Fintype I](R:Run G)(d:I→ℕ){D:I→ℕ}
variable (κ:(i:I)→Knob (D i))(pt:I→Chamber)(q:(i:I)→Choice R d i)
local notation "hi_" => WilsonOlderFreshSoftSocketPole.raw R d κ pt q
local notation "lo_" => WilsonReceivedCanonicalVerseRegister.offer R d κ pt q
local notation "lag_" => WilsonOlderFreshSoftSocketPole.lag R d q
variable (z:I → Cover)(A:Case D)(n:Side)

theorem ordinary (S:Finset I):
    readO A (levelsO (independent (hi_) z) S) n=
      PowerSeries.X^(∑i∈S,lag_ i)*readO A (levelsO (start R d κ pt q z) S) n:=by
  classical
  have paidH:Eu d (independent (hi_) z):=legal _ _ fun i _=>Nat.le_add_left _ _
  have paidL:Eu d (independent (lo_) z):=legal _ _ fun i _=>WilsonReceivedCanonicalVerseBasis.grade R d κ pt i (q i)
  have top:=levels_exp _ paidH (IndependentSourcePathFamily.empty _ _) A n
  have low:=levels_exp _ paidL (IndependentSourcePathFamily.empty _ _) A n
  let X:=@PowerSeries.X (MvPolynomial (Woods G n) ℝ) _
  have same:=SignedJointSourceMoments.transported (lag_) X (RingHom.id _) low
  have incoming:feeble (independent (hi_) z) A n=
      SignedJointSourceMoments.pushed (lag_) X (RingHom.id _) (feeble (independent (lo_) z) A n):=by
    funext s
    change readO A (independent (hi_) z s) n=X^(_)*readO A (independent (lo_) z s) n
    by_cases one:∃i,s={i}
    · obtain ⟨i,rfl⟩:=one
      rw [IndependentSourcePathFamily.singleton,IndependentSourcePathFamily.singleton]
      simpa [SignedJointSourceMoments.clearing,X] using WilsonOlderFreshSoftSocketPole.radial R d κ pt q i (z i) n A
    · have blank:=fun i h=>one ⟨i,h⟩
      rw [dark _ z s blank,dark _ z s blank,read_emp,mul_zero]
  rw [←incoming] at same
  exact congrFun (Equation.prod_u _ _ _ top same) S

end YM.Integration.WilsonOlderFreshSoftSocketOpening
end
