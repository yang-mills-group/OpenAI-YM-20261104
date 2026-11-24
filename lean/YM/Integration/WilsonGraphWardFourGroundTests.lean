import YM.Integration.WilsonGraphWardGroundDifference
import YM.Integration.WilsonGraphIndependentSignedStress
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneFourSmearedWardReadings
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneFiniteWardMatrix

/-! Uniqueness on the two actual magnetic probes, the vacuum pupil and the
translation window of the public stress comparison. -/
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1600000
namespace YM.Integration.WilsonGraphWardFourGroundTests
open _root_.YangMills _root_.YangMills.Matching _root_.YangMills.Matching.WardStress
open _root_.PhysicalMatching.H7StandaloneFourSmearedWardReadings (Pupils probes)
open _root_.PhysicalMatching.H7StandaloneAppointedPublicWardRows (columns)
open _root_.PhysicalMatching.H7StandaloneFiniteWardMatrix (act)
open MeasureTheory
open scoped Classical BigOperators


def rows {g : GaugeGroup} (M : MSbar.Coefficients (_root_.IssuedMaxwell.Reports.B g)) (S : Conversion (_root_.IssuedMaxwell.Reports.B g)) (hg : g.core.Simple)
    (pupils : Pupils) (F G : Axis → Axis → (_root_.IssuedMaxwell.Reports.B g).sector 4) : Fin 4 → ℂ :=
  let vacuum := ∫ x : Points 1, pupils.vacuum x *
    GroundDifference.ground M S (F 0 0) (G 0 0) (fun i : Fin 0 => Fin.elim0 i) x
  let divergence := fun row : Fin 2 => ∑ j : Fin 2, ∑ a : Axis, ∫ x : Points 2,
    _root_.YangMills.Ward.firstDerivative a (fun y => pupils.conservation row j y) x *
      GroundDifference.ground M S (F a 0) (G a 0) (fun _ : Fin 1 => ⟨4, probes hg j⟩) x
  let flux := -(∑ a : Axis, ∫ z : Spacetime × Points 2,
    pupils.translation z.2 * ((_root_.YangMills.Maxwell.partialD a pupils.cutoff z.1 : ℝ) : ℂ) *
      GroundDifference.ground M S (F a 0) (G a 0) (fun _ : Fin 2 => ⟨4, probes hg 0⟩)
        (_root_.YangMills.Ward.prepend z.1 z.2))
  ![vacuum, divergence 0, divergence 1, flux]



theorem filed {g : GaugeGroup} {M : MSbar.Coefficients (_root_.IssuedMaxwell.Reports.B g)} {S : Conversion (_root_.IssuedMaxwell.Reports.B g)}
    {P Q : Series (_root_.IssuedMaxwell.Reports.B g)} (hg : g.core.Simple) (pupils : Pupils)
    (p : Determined M S P) (q : Determined M S Q)
    (k : ℕ) (earlier : ∀ j < k, P j = Q j) :
    rows M S hg pupils (P k) (Q k) = 0 := by
  classical
  have vacuum := (GroundDifference.vacuum p q k earlier 0 0 pupils.vacuum).2
  have divergence (row : Fin 2) :
      (∑ j : Fin 2, ∑ a : Axis, ∫ x : Points 2,
        _root_.YangMills.Ward.firstDerivative a (fun y => pupils.conservation row j y) x *
          GroundDifference.ground M S (P k a 0) (Q k a 0)
            (fun _ : Fin 1 => ⟨4, probes hg j⟩) x) = 0 :=
    Finset.sum_eq_zero (fun j _ => (GroundDifference.conservation p q k earlier 0
      (fun _ : Fin 1 => ⟨4, probes hg j⟩) (pupils.conservation row j)).2)
  have flux := (GroundDifference.translation p q k earlier 0
    (fun _ : Fin 2 => ⟨4, probes hg 0⟩) pupils.translation pupils.cutoff pupils.window).2
  funext i
  fin_cases i
  · exact vacuum
  · exact divergence 0
  · exact divergence 1
  · exact neg_eq_zero.mpr flux

theorem unique {g : GaugeGroup} {M : MSbar.Coefficients (_root_.IssuedMaxwell.Reports.B g)} {S : Conversion (_root_.IssuedMaxwell.Reports.B g)}
    {P Q : Series (_root_.IssuedMaxwell.Reports.B g)} (hg : g.core.Simple) (pupils : Pupils) (L : Matrix (Fin 4) (Fin 4) ℂ)
    (groundRows : ∀ u w : Fin 4 → ℂ,
      rows M S hg pupils (fun a b => ∑ l, u l • columns hg a b l)
        (fun a b => ∑ l, w l • columns hg a b l) = act L u - act L w)
    (injective : Function.Injective (act L))
    (p : Determined M S P) (q : Determined M S Q) : P = Q := by
  classical
  funext k
  induction k using Nat.strong_induction_on with
  | h k earlier =>
    obtain ⟨u, hu⟩ := YM.UVNext.FreeStress.Independent.original hg p k
    obtain ⟨w, hw⟩ := YM.UVNext.FreeStress.Independent.original hg q k
    have hP : P k = fun a b => ∑ l, u l • columns hg a b l :=
      funext (fun a => funext (hu a))
    have hQ : Q k = fun a b => ∑ l, w l • columns hg a b l :=
      funext (fun a => funext (hw a))
    have zero := filed hg pupils p q k earlier
    rw [hP, hQ] at zero
    have difference : act L u - act L w = 0 := (groundRows u w).symm.trans zero
    have same : u = w := injective (sub_eq_zero.mp difference)
    exact hP.trans ((congrArg
      (fun c : Fin 4 → ℂ => fun a b => ∑ l, c l • columns hg a b l) same).trans hQ.symm)

end YM.Integration.WilsonGraphWardFourGroundTests
end

