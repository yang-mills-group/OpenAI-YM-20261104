import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedPhysicalConversionEntry
import Mathlib.RingTheory.PowerSeries.Inverse
namespace IssuedBridge.PostedOriginalFieldInverse
open YM YM.Integration YM.MS YM.MS.Land YM.MS.Fleet YM.FVA2 YM.FVA2.Scale YM.FVA2.Register YM.XSpace.Normalize Finset
open scoped Classical BigOperators
noncomputable section
private theorem composition {E : Type*} [AddCommGroup E] [Module ℂ E]
    (A B : PowerSeries (Module.End ℂ E)) (k : ℕ) :
    (∑ i : Fin (k+1), (PowerSeries.coeff i.val A).comp (PowerSeries.coeff (k-i.val) B)) =
      PowerSeries.coeff k (A * B) := by
  change (∑ i : Fin (k+1), PowerSeries.coeff i.val A * PowerSeries.coeff (k-i.val) B) = _
  rw [PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff a A * PowerSeries.coeff b B) k,
    ← Fin.sum_univ_eq_sum_range (fun a => PowerSeries.coeff a A * PowerSeries.coeff (k-a) B) (k+1)]

private theorem inverse {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : PowerSeries (Module.End ℂ E)) (ground : PowerSeries.constantCoeff F = 1) :
    let inv := PowerSeries.invOfUnit F 1
    ∀ k : ℕ,
      (∑ i : Fin (k+1), (PowerSeries.coeff i.val inv).comp (PowerSeries.coeff (k-i.val) F)) =
        (if k = 0 then LinearMap.id else 0) ∧
      (∑ i : Fin (k+1), (PowerSeries.coeff i.val F).comp (PowerSeries.coeff (k-i.val) inv)) =
        (if k = 0 then LinearMap.id else 0) := by
  dsimp only
  intro k
  have left := PowerSeries.invOfUnit_mul F (1 : (Module.End ℂ E)ˣ) ground
  have right := PowerSeries.mul_invOfUnit F (1 : (Module.End ℂ E)ˣ) ground
  constructor
  · rw [composition, left, PowerSeries.coeff_one]
    split <;> rfl
  · rw [composition, right, PowerSeries.coeff_one]
    split <;> rfl

theorem original {G : Gauge} (Z : WilsonPrescription G)
    (raw : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {S : Prescription (Press.portDeck G)} {simple : G.Simple} {dial : Bool}
    (matched : Main.Match Z simple raw S dial) (μ : ℝ) (d : ℕ) :
    let F := Measure.Z Z.scheme Z.criterion μ raw d
    let inv := PowerSeries.invOfUnit F 1
    ∀ k : ℕ,
      (∑ i : Fin (k+1), (PowerSeries.coeff i.val inv).comp (PowerSeries.coeff (k-i.val) F)) =
        (if k = 0 then LinearMap.id else 0) ∧
      (∑ i : Fin (k+1), (PowerSeries.coeff i.val F).comp (PowerSeries.coeff (k-i.val) inv)) =
        (if k = 0 then LinearMap.id else 0) :=
  inverse (Measure.Z Z.scheme Z.criterion μ raw d) (matched.frame μ d).1.lead

end
end IssuedBridge.PostedOriginalFieldInverse
