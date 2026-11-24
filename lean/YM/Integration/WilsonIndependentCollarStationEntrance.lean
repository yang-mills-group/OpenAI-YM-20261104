import YM.Integration.WilsonIndependentCollarRestoredOrbit
import YM.Integration.WilsonIndependentCollarOrbitShapes
import YM.Integration.WilsonIndependentCollarDatedUpperBasis

/-! The signed coefficients in the physical station estimate restore the
original uncut canonical functions, including the unit, on every fine field. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarStationEntrance
open Function Finset Lattice Wilson RG Next.Foundations
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Mer WilsonCoeffUV.Embroider
open WilsonReceivedCanonicalVerseBasis WilsonOriginalStarSceneWords WilsonThermometerDeclaredSeeds
open PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonIndependentCollarPaidWindingPanel (signed)
open WilsonIndependentCollarOrbitalBasisPayment (Choices)
open scoped Classical BigOperators

variable {G:Gauge}{n:ℕ}(R:Run G)(k D:Fin n→ℕ)(κ:(j:Fin n)→Knob (D j))(pt:Fin n→Chamber)

theorem crop {side:Side}(g:ℝ)(j:Fin n)(a:Choice R k j)(y:Site side)(U:Config G side):
    restored R k κ pt g j a y U=
      (Complex.ofReal ((g⁻¹)^(pole R k (entry R k j a))))*↑((raw R k (entry R k j a)).unmasked U y):=by
  dsimp only [restored]
  rw [field R k κ pt j a U y]
  simp

include κ pt in
theorem original (N per K m:ℕ)(live:K≤N)(v:(j:Fin n)→R.family.label (k j))
    (target:Finset (Fin n))(y:Fin n→Site (R.family.side K per))(U:Config G (R.family.side K per)):
    let size:=R.family.path.levels.S.a m/R.family.path.levels.S.a K
    (∏j:target,Complex.ofReal (size^(k j)))*(∏j:target,
      WilsonPositionProgramBlockedTrialAddBack.uncut R (k j) N per K (y j) (v j) U)=
      ∑a:Choices R k target,signed R k N per K m v target a *
        ∏j:target,(↑((raw R k (entry R k j (a j))).unmasked U (y j)):ℂ):=by
  intro size
  rw [faces R k κ pt N per K live v y target U,Finset.mul_sum]
  apply sum_congr rfl;intro a _
  unfold signed
  rw [←prod_mul_distrib,←prod_mul_distrib,←prod_mul_distrib]
  apply prod_congr rfl;intro j _
  rw [crop R k D κ pt]
  simp only [Complex.ofReal_mul];ring

end YM.Integration.WilsonIndependentCollarStationEntrance
end
