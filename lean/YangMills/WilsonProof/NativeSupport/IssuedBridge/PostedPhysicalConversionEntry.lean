import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedFieldSubstitution
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedThermalTruncation
namespace IssuedBridge.PostedPhysicalConversionEntry
open YM YM.Integration YM.MS YM.MS.Land YM.MS.Fleet YM.FVA2 YM.FVA2.Register YM.FVA2.Scale
open YM.XSpace YM.XSpace.Normalize YangMills.Matching
open scoped Classical BigOperators
noncomputable section

theorem original {G : Gauge} (Z : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {S : Prescription (Press.portDeck G)} {simple : G.Simple} {dial : Bool}
    (matched : Main.Match Z simple M S dial) (μ : ℝ) (f : ℕ → ℝ)
    (coupling : ∀ i, PowerSeries.coeff i (Measure.f Z.criterion μ M) = (f i : ℂ))
    {n h : ℕ} (x : Stage n) (v : Fin n → Sec G h) (k : ℕ) :
    Measure.outlook Z.scheme Z.criterion h n x k v =
      ∑ ν : Fin n → Fin (k+1), ∑ j : Fin (k+1),
        if (∑ i, (ν i).val) ≤ k then (couplingPower f j.val (k-∑ i, (ν i).val) : ℂ) *
          Equator.wave μ M h n x j.val (fun i => (PowerSeries.coeff (ν i).val
            (Measure.Z Z.scheme Z.criterion μ M h)) (v i)) else 0 := by
  classical
  rw [← matched.eqconv μ h]
  change Dframe.status (Measure.Z Z.scheme Z.criterion μ M h)
    ((Book.Program.substitute (Measure.f Z.criterion μ M)) (Equator.wave μ M h n x)) k v = _
  rw [PostedFieldSubstitution.original]
  apply Finset.sum_congr rfl
  intro ν _
  split_ifs with within
  · have cut := PostedThermalTruncation.original (Measure.f Z.criterion μ M)
      (matched.positionCoupling μ).1.start (Equator.wave μ M h n x)
      (show k-∑ i, (ν i).val ≤ k from Nat.sub_le _ _)
    rw [cut]
    simp only [sum_apply, smul_apply, smul_eq_mul,
      PostedCouplingPowers.original _ f coupling]
  · simp
end
end IssuedBridge.PostedPhysicalConversionEntry
