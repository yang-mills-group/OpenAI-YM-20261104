import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneFourSmearedWardReadings

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace PhysicalMatching.H7IndependentFourMaxwellWardReadings
open MeasureTheory
open scoped BigOperators Classical
open PhysicalMatching.H7StandaloneFourSmearedWardReadings
open PhysicalMatching.H7StandaloneAppointedPublicWardRows
variable {g : YangMills.GaugeGroup}

def freeMarked {n : ℕ} (w : (YangMills.maxwellReference g).sector 4)
    (q : Fin n → (YangMills.maxwellReference g).sector 4) (x : YangMills.Points (n+1)) : ℂ :=
  (YangMills.maxwellReference g).moment x (Fin.cons w.val (fun i => (q i).val))

def freeMatrix (hg : g.core.Simple) (P : Pupils) : Matrix (Fin 4) (Fin 4) ℂ := fun i k =>
  ![∫ x : YangMills.Points 1, P.vacuum x *
      freeMarked (columns hg 0 0 k) (fun j : Fin 0 => Fin.elim0 j) x,
    ∑ j : Fin 2, ∑ a : YM.Axis, ∫ x : YangMills.Points 2,
      YangMills.Ward.firstDerivative a (fun y => P.conservation 0 j y) x *
        freeMarked (columns hg a 0 k) (fun _ : Fin 1 => probes hg j) x,
    ∑ j : Fin 2, ∑ a : YM.Axis, ∫ x : YangMills.Points 2,
      YangMills.Ward.firstDerivative a (fun y => P.conservation 1 j y) x *
        freeMarked (columns hg a 0 k) (fun _ : Fin 1 => probes hg j) x,
    -(∑ a : YM.Axis, ∫ z : YangMills.Spacetime × YangMills.Points 2,
      P.translation z.2 * ((YangMills.Maxwell.partialD a P.cutoff z.1 : ℝ) : ℂ) *
        freeMarked (columns hg a 0 k) (fun _ : Fin 2 => probes hg 0)
          (YangMills.Ward.prepend z.1 z.2))] i

def freeRightSide (hg : g.core.Simple) (P : Pupils) : Fin 4 → ℂ :=
  ![0, 0, 0, -(∫ x : YangMills.Points 2,
    YangMills.Ward.firstDerivative 0 (fun y => P.translation y) x *
      (YangMills.maxwellReference g).moment x (fun _ : Fin 2 => (probes hg 0).val))]

def derivativeBlock (hg : g.core.Simple) (x : YangMills.Points 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun j k => YangMills.Ward.firstDerivative 0 (fun y : YangMills.Points 2 =>
    freeMarked (columns hg 0 0 ((![1,2] : Fin 2 → Fin 4) k))
      (fun _ : Fin 1 => probes hg j) y) x

def squareDerivative (hg : g.core.Simple) (x : YangMills.Points 2) : ℂ :=
  YangMills.Ward.firstDerivative 0 (fun y : YangMills.Points 2 =>
    (YangMills.maxwellReference g).moment y (fun _ : Fin 2 => (probes hg 0).val)) x

def detTwo (D : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := D 0 0 * D 1 1 - D 0 1 * D 1 0

def reciprocal (D : Matrix (Fin 2) (Fin 2) ℂ) (v : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun r j => v * (![![D 1 1, -D 0 1], ![-D 1 0, D 0 0]] r j) / detTwo D

def conservationProfile (hg : g.core.Simple) (ψ : YangMills.Points 2 → ℝ)
    (r j : Fin 2) (x : YangMills.Points 2) : ℂ := reciprocal (derivativeBlock hg x) (ψ x) r j

def translationProfile (hg : g.core.Simple) (ψ : YangMills.Points 2 → ℝ)
    (x : YangMills.Points 2) : ℂ := (ψ x : ℂ) / squareDerivative hg x

theorem normalizedConservation (hg : g.core.Simple) (ψ : YangMills.Points 2 → ℝ)
    (x : YangMills.Points 2) (hx : detTwo (derivativeBlock hg x) ≠ 0) (r k : Fin 2) :
    (∑ j : Fin 2, conservationProfile hg ψ r j x * derivativeBlock hg x j k) =
      if r = k then (ψ x : ℂ) else 0 := by
  let D := derivativeBlock hg x
  change (∑ j : Fin 2, reciprocal D (ψ x) r j * D j k) = _
  have hd : detTwo D ≠ 0 := hx
  fin_cases r <;> fin_cases k <;> simp [reciprocal, Fin.sum_univ_succ] <;>
    field_simp [hd] <;> unfold detTwo <;> ring

theorem normalizedTranslation (hg : g.core.Simple) (ψ : YangMills.Points 2 → ℝ)
    (x : YangMills.Points 2) (hx : squareDerivative hg x ≠ 0) :
    translationProfile hg ψ x * squareDerivative hg x = (ψ x : ℂ) := by
  exact div_mul_cancel₀ _ hx

def leading (fluxQ fluxS : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![1,0,0,0], ![0,-1,0,0], ![0,0,-1,0], ![0,fluxQ,fluxS,1]]

theorem inverseMatrix (a b : ℂ) : leading a b * leading a b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leading, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

theorem inverseAction (a b : ℂ) (y : Fin 4 → ℂ) :
    (leading a b).mulVec y = ![y 0, -y 1, -y 2, a*y 1 + b*y 2 + y 3] := by
  funext i
  fin_cases i <;> simp [leading, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem groundStress (a b : ℂ) :
    (leading a b).mulVec (![0,0,0,1] : Fin 4 → ℂ) = ![0,0,0,1] := by
  rw [inverseAction]
  simp

theorem inverseOnActualRows (hg : g.core.Simple) (P : Pupils)
    (rows : freeMatrix hg P = leading (freeMatrix hg P 3 1) (freeMatrix hg P 3 2)) :
    freeMatrix hg P * freeMatrix hg P = 1 := by
  calc
    _ = leading (freeMatrix hg P 3 1) (freeMatrix hg P 3 2) *
          leading (freeMatrix hg P 3 1) (freeMatrix hg P 3 2) := congrArg₂ (· * ·) rows rows
    _ = 1 := inverseMatrix _ _

end PhysicalMatching.H7IndependentFourMaxwellWardReadings
end
