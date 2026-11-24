import YM.Integration.WilsonOriginalTwoFlatRoseSecant
import YM.Integration.WilsonMaxwellThermometerNominatedCofactor

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatRoseNominated
open Function Finset MeasureTheory Lattice RG Wilson Source Labels Extra.Histories RG16.Literal
open PhysicalNext.Repeat.Legato Planned.GuardedAtom Trace.Physical.GermGraph
open WilsonOriginalTwoFlatGridScaling (gap)
open WilsonThermometerUnitFilingFlatTelescope (numerator feeAt)
open WilsonOriginalTwoFlatRoseIdentity (entry cross figure)
open WilsonPositionThermometerCapStation
open WilsonNeutralOffsetCutoff (named)
open WilsonThermometerAlignedCells (atOrigin)
open WilsonMaxwellThermometerNominatedCofactor (native)
open OPE OPE.Orbits Extraction Spec Table XSpace XSpace.Rose
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(A:WilsonPositionThermometerCapStation.Group R.family 6){N per:ℕ}
local notation "X" j:max => Config G (R.family.side j per)
local notation "S" => Site (R.family.side N per)
local notation "E" => Finset (Fin 3)

def face (y:S×S)(s:E):Cut R.family N per:=
  fun U=>∏i∈s,R.family.O N per (named R A N per i) (atOrigin y i) U

theorem paid (y:S×S)(s:E):Continuous (face R A y s):=
  continuous_finsetProd _ fun i _=>R.family.continuousO N per _ (named R A N per i) (atOrigin y i)

/-- Read the nominated upper clover at the actual origin, against both named lower
arms. The finite weight sums one common translation of the relative pair. -/
theorem original (φ:Test 3)(r:ℝ){K c u v:ℕ}(uc:u≤c)(vc:v≤c)(ck:c≤K)(kn:K≤N)
    (M:S×S → E → (j:ℕ) → X j → ℂ)(Q:S×S → E → ℂ)
    (registered:∀(y:S×S)(s:E)(j:ℕ),min u v≤j → j≤K →
      Integrable (numerator R N per j (M y s j)) (prior G _)):
    ∑y:S×S,WilsonThermometerAlignedCells.mass (R:=R) r (N,per) φ y*
      (WilsonMaxwellThermometerNominatedCofactor.reading R A N per y (native R A N per y 0)-
        WilsonPositionThermometerConnected.value (Q y))=
      ∑y:S×S,WilsonThermometerAlignedCells.mass (R:=R) r (N,per) φ y*
        ∑s:E,WilsonMaxwellThermometerNominatedSecant.bill (fun t=>R.family.omega N per (face R A y t)) (Q y) s*
          (gap R N per u ((uc.trans ck).trans kn) (face R A y s)+entry R (uc.trans ck) kn (face R A y s) (M y s)+
            (∑j∈Ico c K,feeAt R N per u (M y s) j)+cross R (N:=N) uc vc (M y s)+
            (∑j∈Ico v c,feeAt R N per v (M y s) j)+(M y s v 1-Q y s)):=by
  apply sum_congr rfl
  intro y _
  apply congrArg (_*·)
  rw [WilsonMaxwellThermometerNominatedCofactor.original,WilsonMaxwellThermometerNominatedSecant.signed]
  apply sum_congr rfl
  intro s _
  exact congrArg (_*·) (figure R uc vc ck kn (face R A y s) (paid R A y s) (M y s) (registered y s) (Q y s))

end YM.Integration.WilsonOriginalTwoFlatRoseNominated
end
