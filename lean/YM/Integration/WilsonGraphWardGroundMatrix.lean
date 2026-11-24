import YM.Integration.WilsonGraphWardGroundColumns
import YM.Integration.WilsonGraphWardFourGroundTests

/-! The four filed signed Ward tests on the independent Maxwell columns. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonGraphWardGroundMatrix
open _root_.YangMills _root_.YangMills.Matching _root_.YangMills.Matching.WardStress
open _root_.YangMills.MSbar.Ordinary (Label)
open _root_.PhysicalMatching.H7StandaloneFourSmearedWardReadings (Pupils probes)
open _root_.PhysicalMatching.H7StandaloneAppointedPublicWardRows (columns)
open _root_.PhysicalMatching.H7StandaloneFiniteWardMatrix (act)
open _root_.YM.Integration.WilsonGraphGroupGroundMultilinear (labels)
open MeasureTheory
open scoped BigOperators Classical
variable {g : GaugeGroup}

def reading (S : Conversion (_root_.IssuedMaxwell.Reports.B g)) {n : ℕ} (v : Fin n → (_root_.IssuedMaxwell.Reports.B g).sector 4)
    (f : (_root_.IssuedMaxwell.Reports.B g).sector 4) (x : Points (n + 1)) : ℂ :=
  S.correlation (_root_.IssuedMaxwell.GraphCoefficients.issued g) 0 (Fin.cons ⟨4, f⟩ (fun i => ⟨4, v i⟩)) x

private theorem point_eq (S : Conversion (_root_.IssuedMaxwell.Reports.B g)) {n : ℕ} (v : Fin n → (_root_.IssuedMaxwell.Reports.B g).sector 4)
    (f : (_root_.IssuedMaxwell.Reports.B g).sector 4) (x : Points (n + 1)) :
    WilsonGraphWardGroundColumns.point g S (fun _ : Fin (n + 1) => 4)
      (Fin.cons (0 : (_root_.IssuedMaxwell.Reports.B g).sector 4) v) f x = reading S v f x := by
  classical
  unfold WilsonGraphWardGroundColumns.point reading
  have h : labels g (fun _ : Fin (n + 1) => 4)
      (Function.update (Fin.cons (0 : (_root_.IssuedMaxwell.Reports.B g).sector 4) v) 0 f) =
      Fin.cons (⟨4, f⟩ : _root_.YangMills.Matching.Label (_root_.IssuedMaxwell.Reports.B g)) (fun i => ⟨4, v i⟩) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [labels]
    · simp [labels, Fin.succ_ne_zero]
  rw [h]

theorem tested (S : Conversion (_root_.IssuedMaxwell.Reports.B g)) {n : ℕ} (v : Fin n → (_root_.IssuedMaxwell.Reports.B g).sector 4)
    {X : Type*} [MeasureSpace X] (shape : X → Points (n + 1)) (weight : X → ℂ)
    (occupied : ∀ z, weight z ≠ 0 → shape z ∈ separated (n + 1))
    (u w : Fin 4 → ℂ) (col : Fin 4 → (_root_.IssuedMaxwell.Reports.B g).sector 4)
    (paid : ∀ l, Integrable (fun z => weight z * reading S v (col l) (shape z))) :
    (∫ z, weight z * GroundDifference.ground (_root_.IssuedMaxwell.GraphCoefficients.issued g) S
      (∑ l, u l • col l) (∑ l, w l • col l) (fun i => ⟨4, v i⟩) (shape z)) =
      ∑ l, (u l - w l) * ∫ z, weight z * reading S v (col l) (shape z) := by
  classical
  have h := WilsonGraphWardGroundColumns.integrated g S
    (fun _ : Fin (n + 1) => 4) (Fin.cons (0 : (_root_.IssuedMaxwell.Reports.B g).sector 4) v) shape weight
    occupied u w col (fun l => by simpa only [point_eq] using paid l)
  simpa only [point_eq, reading, GroundDifference.ground] using h

theorem zeroReading (S : Conversion (_root_.IssuedMaxwell.Reports.B g)) {n : ℕ} (v : Fin n → (_root_.IssuedMaxwell.Reports.B g).sector 4)
    (x : Points (n + 1)) (hx : x ∈ separated (n + 1)) : reading S v 0 x = 0 := by
  classical
  have h := WilsonGraphWardGroundColumns.finiteFirst g S
    (fun _ : Fin (n + 1) => 4) (Fin.cons (0 : (_root_.IssuedMaxwell.Reports.B g).sector 4) v) x hx
    (fun i : Fin 0 => (Fin.elim0 i : ℂ)) (fun i : Fin 0 => (Fin.elim0 i : (_root_.IssuedMaxwell.Reports.B g).sector 4))
  simpa [point_eq] using h

def Tested (S : Conversion (_root_.IssuedMaxwell.Reports.B g)) (hg : g.core.Simple) {n : ℕ} (a : Axis)
    (t : Fin n → Fin 2) {X : Type*} [MeasureSpace X]
    (shape : X → Points (n + 1)) (weight : X → ℂ) : Prop :=
  (∀ z, weight z ≠ 0 → shape z ∈ separated (n + 1)) ∧
    ∀ l, Integrable (fun z => weight z *
      reading S (fun i => probes hg (t i)) (columns hg a 0 l) (shape z))

private theorem oneTest (S : Conversion (_root_.IssuedMaxwell.Reports.B g)) (hg : g.core.Simple) {n : ℕ} (a : Axis)
    (t : Fin n → Fin 2) {X : Type*} [MeasureSpace X]
    (shape : X → Points (n + 1)) (weight : X → ℂ) (paid : Tested S hg a t shape weight)
    (u w : Fin 4 → ℂ) :
    (∫ z, weight z * GroundDifference.ground (_root_.IssuedMaxwell.GraphCoefficients.issued g) S
      (∑ l, u l • columns hg a 0 l) (∑ l, w l • columns hg a 0 l)
      (fun i => ⟨4, probes hg (t i)⟩) (shape z)) =
      ∑ l, (u l - w l) * ∫ z, weight z * GroundDifference.ground (_root_.IssuedMaxwell.GraphCoefficients.issued g) S
        (columns hg a 0 l) 0 (fun i => ⟨4, probes hg (t i)⟩) (shape z) := by
  refine (tested S (fun i => probes hg (t i)) shape weight paid.1 u w (columns hg a 0) paid.2).trans ?_
  apply Finset.sum_congr rfl
  intro l _
  apply congrArg (fun b : ℂ => (u l - w l) * b)
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases h : weight z = 0
  · simp [h]
  · change weight z * reading S _ _ _ =
      weight z * (reading S _ _ _ - reading S (fun i => probes hg (t i)) 0 (shape z))
    rw [zeroReading S _ _ (paid.1 z h), sub_zero]

private theorem sumTests {ι : Type*} [Fintype ι] (c : Fin 4 → ℂ)
    (f : ι → ℂ) (e : ι → Fin 4 → ℂ) (h : ∀ i, f i = ∑ l, c l * e i l) :
    (∑ i, f i) = ∑ l, c l * ∑ i, e i l := by
  classical
  calc
    (∑ i, f i) = ∑ i, ∑ l, c l * e i l := Finset.sum_congr rfl (fun i _ => h i)
    _ = ∑ l, ∑ i, c l * e i l := Finset.sum_comm
    _ = _ := by simp only [Finset.mul_sum]

def matrix (S : Conversion (_root_.IssuedMaxwell.Reports.B g)) (hg : g.core.Simple) (P : Pupils) :
    Matrix (Fin 4) (Fin 4) ℂ := fun i l =>
  WilsonGraphWardFourGroundTests.rows (_root_.IssuedMaxwell.GraphCoefficients.issued g) S hg P
    (fun a b => columns hg a b l) (fun _ _ => 0) i

set_option maxHeartbeats 1600000 in
theorem groundRows (S : Conversion (_root_.IssuedMaxwell.Reports.B g)) (hg : g.core.Simple) (P : Pupils)
    (vacuum : Tested S hg (X := Points 1) 0 (fun i : Fin 0 => Fin.elim0 i) id (fun x => P.vacuum x))
    (conservation : ∀ row j : Fin 2, ∀ a : Axis, Tested S hg (X := Points 2) a (fun _ : Fin 1 => j) id
      (fun x => _root_.YangMills.Ward.firstDerivative a (fun y => P.conservation row j y) x))
    (translation : ∀ a : Axis, Tested S hg a (fun _ : Fin 2 => 0)
      (fun z : Spacetime × Points 2 => _root_.YangMills.Ward.prepend z.1 z.2)
      (fun z => P.translation z.2 *
        ((_root_.YangMills.Maxwell.partialD a P.cutoff z.1 : ℝ) : ℂ)))
    (u w : Fin 4 → ℂ) :
    WilsonGraphWardFourGroundTests.rows (_root_.IssuedMaxwell.GraphCoefficients.issued g) S hg P
      (fun a b => ∑ l, u l • columns hg a b l) (fun a b => ∑ l, w l • columns hg a b l) =
      act (matrix S hg P) u - act (matrix S hg P) w := by
  classical
  have emptyLabels : (fun i : Fin 0 => (⟨4, probes hg (Fin.elim0 i)⟩ : _root_.YangMills.Matching.Label (_root_.IssuedMaxwell.Reports.B g))) =
      (fun i : Fin 0 => (Fin.elim0 i : _root_.YangMills.Matching.Label (_root_.IssuedMaxwell.Reports.B g))) := funext (fun i => Fin.elim0 i)
  funext i
  trans ∑ l, (u l - w l) * matrix S hg P i l
  · have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl
    · simp only [matrix, WilsonGraphWardFourGroundTests.rows, Matrix.cons_val_zero]
      simpa only [emptyLabels, id_eq] using
        (oneTest S hg (X := Points 1) 0 (fun i : Fin 0 => Fin.elim0 i) id (fun x => P.vacuum x) vacuum u w)
    · rw [show (1 : Fin 4) = Fin.succ ((0 : Fin 3)) by rfl]
      simp only [matrix, WilsonGraphWardFourGroundTests.rows, Matrix.cons_val_succ, Matrix.cons_val_zero]
      refine sumTests (fun l => u l - w l) _ _ ?_
      intro j
      refine sumTests (fun l => u l - w l) _ _ ?_
      intro a
      simpa only [id_eq] using
        (oneTest S hg (X := Points 2) a (fun _ : Fin 1 => j) id _ (conservation 0 j a) u w)
    · rw [show (2 : Fin 4) = Fin.succ (Fin.succ ((0 : Fin 2))) by rfl]
      simp only [matrix, WilsonGraphWardFourGroundTests.rows, Matrix.cons_val_succ, Matrix.cons_val_zero]
      refine sumTests (fun l => u l - w l) _ _ ?_
      intro j
      refine sumTests (fun l => u l - w l) _ _ ?_
      intro a
      simpa only [id_eq] using
        (oneTest S hg (X := Points 2) a (fun _ : Fin 1 => j) id _ (conservation 1 j a) u w)
    · rw [show (3 : Fin 4) = Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))) by rfl]
      simp only [matrix, WilsonGraphWardFourGroundTests.rows, Matrix.cons_val_succ, Matrix.cons_val_zero]
      simp only [mul_neg, Finset.sum_neg_distrib, neg_inj]
      refine sumTests (fun l => u l - w l) _ _ ?_
      intro a
      exact oneTest S hg a (fun _ : Fin 2 => 0) _ _ (translation a) u w
  · simp only [act, Pi.sub_apply, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun l _ => by ring)

end YM.Integration.WilsonGraphWardGroundMatrix
end

