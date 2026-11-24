import YM.Integration.WilsonMSbarCorrelationHeatAllocation
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandalonePhysicalWardCalibration
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneTranslationTestSupport

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace YM.Integration.WilsonGraphWardExtensional

open YangMills YangMills.Matching YangMills.Matching.CorrelationOnly
open Set Filter MeasureTheory
open scoped Topology BigOperators Classical

variable {g : YangMills.GaugeGroup} {B : YangMills.Maxwell.Reference g}
variable {M N : YangMills.MSbar.Coefficients B}

def SeparatedRead (M N : YangMills.MSbar.Coefficients B) : Prop :=
  ∀ {n : ℕ} (k : ℕ) (v : Fin n → Label B) (x : YangMills.Points n),
    x ∈ YangMills.separated n → M.correlation n k v x = N.correlation n k v x

theorem through (read : SeparatedRead M N) (S : Conversion B) {n : ℕ}
    (k : ℕ) (v : Fin n → Label B) (x : YangMills.Points n) (hx : x ∈ YangMills.separated n) :
    S.correlation M k v x = S.correlation N k v x := by
  rw [allocated S M k v x, allocated S N k v x]
  apply Finset.sum_congr rfl
  intro heat _
  apply Finset.sum_congr rfl
  intro j _
  rw [read j.val (S.inputs v heat) x hx]

theorem inserted (read : SeparatedRead M N) (S : Conversion B) (P : WardStress.Series B)
    {n : ℕ} (k : ℕ) (a b : YangMills.Axis) (v : Fin n → Label B)
    (x : YangMills.Points (n+1)) (hx : x ∈ YangMills.separated (n+1)) :
    WardStress.inserted M S P k a b v x = WardStress.inserted N S P k a b v x := by
  unfold WardStress.inserted
  apply Finset.sum_congr rfl
  intro j _
  exact through read S _ _ x hx

private theorem testZero {n : ℕ} (φ : YangMills.WilsonFamily.SeparatedTest n)
    {x : YangMills.Points n} (outside : x ∉ tsupport (fun y => φ y)) : φ x = 0 := by
  by_contra nonzero
  exact outside (subset_closure (show x ∈ Function.support (fun y => φ y) from nonzero))

theorem firstZero {n : ℕ} (φ : YangMills.WilsonFamily.SeparatedTest (n+1))
    (a : YangMills.Axis) {x : YangMills.Points (n+1)}
    (outside : x ∉ tsupport (fun y => φ y)) :
    YangMills.Ward.firstDerivative a (fun y => φ y) x = 0 := by
  have germ : (fun y => φ y) =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) :=
    notMem_tsupport_iff_eventuallyEq.mp outside
  have derivative : fderiv ℝ (fun y => φ y) x = 0 := by
    simpa using (germ.fderiv_eq (𝕜 := ℝ))
  simp [YangMills.Ward.firstDerivative, derivative]

private theorem firstWeighted {n : ℕ} (φ : YangMills.WilsonFamily.SeparatedTest (n+1))
    (a : YangMills.Axis) (f h : YangMills.Points (n+1) → ℂ)
    (equal : ∀ x ∈ YangMills.separated (n+1), f x = h x) :
    (fun x => YangMills.Ward.firstDerivative a (fun y => φ y) x * f x) =
      (fun x => YangMills.Ward.firstDerivative a (fun y => φ y) x * h x) := by
  funext x
  by_cases member : x ∈ tsupport (fun y => φ y)
  · rw [equal x (φ.tsupport_subset member)]
  · simp only [firstZero φ a member, zero_mul]

def WindowSeparates : Prop :=
  ∀ {n : ℕ} {x : YangMills.Points (n+1)} {χ : YangMills.Spacetime → ℝ},
    x ∈ YangMills.separated (n+1) → YangMills.Ward.Window x χ →
      ∀ (a : YangMills.Axis) (z : YangMills.Spacetime),
        z ∈ tsupport (YangMills.Maxwell.partialD a χ) →
          YangMills.Ward.prepend z x ∈ YangMills.separated (n+2)

theorem flux (separates : WindowSeparates) (read : SeparatedRead M N)
    (S : Conversion B) (P : WardStress.Series B) {n : ℕ} (k : ℕ)
    (v : Fin (n+1) → Label B) (φ : YangMills.WilsonFamily.SeparatedTest (n+1))
    (χ : YangMills.Spacetime → ℝ)
    (window : ∀ x ∈ tsupport (fun y => φ y), YangMills.Ward.Window x χ)
    (a b : YangMills.Axis) :
    WardStress.fluxIntegrand M S P k v φ χ a b =
      WardStress.fluxIntegrand N S P k v φ χ a b := by
  funext z
  by_cases marked : z.2 ∈ tsupport (fun y => φ y)
  · by_cases moving : YangMills.Maxwell.partialD a χ z.1 = 0
    · simp [WardStress.fluxIntegrand, moving]
    · have shell : z.1 ∈ tsupport (YangMills.Maxwell.partialD a χ) :=
        subset_closure (show z.1 ∈ Function.support (YangMills.Maxwell.partialD a χ) from moving)
      have tuple := separates (φ.tsupport_subset marked) (window z.2 marked) a z.1 shell
      simp only [WardStress.fluxIntegrand, inserted read S P k a b v _ tuple]
  · simp [WardStress.fluxIntegrand, testZero φ marked]

theorem transfer (separates : WindowSeparates) (read : SeparatedRead M N)
    (S : Conversion B) (P : WardStress.Series B) (paid : WardStress.Determined M S P) :
    WardStress.Determined N S P := by
  refine ⟨paid.leading, paid.symmetric, paid.signedAxes, ?_, ?_, ?_⟩
  · intro k a b φ
    let empty := fun i : Fin 0 => (Fin.elim0 i : Label B)
    have weighted :
        (fun x => φ x * WardStress.inserted M S P k a b empty x) =
          (fun x => φ x * WardStress.inserted N S P k a b empty x) := by
      funext x
      by_cases member : x ∈ tsupport (fun y => φ y)
      · rw [inserted read S P k a b empty x (φ.tsupport_subset member)]
      · simp only [testZero φ member, zero_mul]
    change Integrable (fun x => φ x * WardStress.inserted N S P k a b empty x) ∧
      (∫ x, φ x * WardStress.inserted N S P k a b empty x) = 0
    rw [← weighted]
    exact paid.vacuum k a b φ
  · intro n k b v φ
    have weighted (a : YangMills.Axis) := firstWeighted φ a
      (fun x => WardStress.inserted M S P k a b v x)
      (fun x => WardStress.inserted N S P k a b v x)
      (fun x hx => inserted read S P k a b v x hx)
    simpa only [← weighted] using paid.conservation k b v φ
  · intro n k b v φ χ window
    have weighted := firstWeighted φ b (S.correlation M k v) (S.correlation N k v)
      (fun x hx => through read S k v x hx)
    have flow (a : YangMills.Axis) := flux separates read S P k v φ χ window a b
    simpa only [← weighted, ← flow] using paid.translation k b v φ χ window

theorem completeRead (S : Conversion B) (equal : M.correlation = N.correlation)
    (P : WardStress.Series B) (paid : WardStress.Determined M S P) :
    WardStress.Determined N S P :=
  determinedAlongCorrelation (fun k v x => converted_eq S M N equal k v x) P paid

theorem windowGeometry : WindowSeparates := by
  intro n x χ hx hw a z hz
  exact _root_.YM.Work.A01.conf_cons hx
    (_root_.PhysicalMatching.H7StandaloneTranslationTestSupport.shellAvoids hw a hz)

theorem determined (read : SeparatedRead M N) (S : Conversion B)
    (P : WardStress.Series B) (paid : WardStress.Determined M S P) :
    WardStress.Determined N S P :=
  transfer windowGeometry read S P paid

theorem oneSeries (S : Conversion B) (actual : YangMills.MSbar.Coefficients B)
    (bank : ∀ n : ℕ, ℕ → (Fin n → Label B) → YangMills.Points n → ℂ)
    (agreement : ∀ {n : ℕ} (k : ℕ) (v : Fin n → Label B) (x : YangMills.Points n),
      x ∈ YangMills.separated n → actual.correlation n k v x = bank n k v x)
    (ground : ∃! P : WardStress.Series B, WardStress.Determined actual S P) :
    ∃ P : WardStress.Series B, WardStress.Determined actual S P ∧
      ∀ candidate : YangMills.MSbar.Coefficients B, candidate.correlation = bank →
        WardStress.Determined candidate S P ∧
          ∀ Q : WardStress.Series B, WardStress.Determined candidate S Q → Q = P := by
  let reference : YangMills.MSbar.Coefficients B := {actual with correlation := bank}
  have forward : SeparatedRead actual reference := agreement
  have back : SeparatedRead reference actual := fun k v x hx => (agreement k v x hx).symm
  obtain ⟨P, paid, unique⟩ := ground
  refine ⟨P, paid, ?_⟩
  intro candidate same
  have eq : reference.correlation = candidate.correlation := same.symm
  refine ⟨completeRead S eq P (determined forward S P paid), ?_⟩
  intro Q accepted
  exact unique Q (determined back S Q (completeRead S eq.symm Q accepted))

end YM.Integration.WilsonGraphWardExtensional
end

