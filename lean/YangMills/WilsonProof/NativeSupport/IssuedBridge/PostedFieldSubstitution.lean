import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedFieldDegreeAllocations
namespace IssuedBridge.PostedFieldSubstitution
open YM YM.XSpace YM.XSpace.Normalize YM.FVA2 YM.FVA2.Scale
open scoped Classical BigOperators
noncomputable section

theorem original {G : Gauge} {n h : ℕ} (Z : Guard G h) (T : ℕ → Structure1.Point G h n)
    (v : Fin n → Sec G h) (k : ℕ) :
    Dframe.status Z T k v = ∑ ν : Fin n → Fin (k+1),
      if (∑ i, (ν i).val) ≤ k then T (k-∑ i, (ν i).val)
        (fun i => (PowerSeries.coeff (ν i).val Z) (v i)) else 0 := by
  classical
  simpa only [Dframe.status, sum_apply, MultilinearMap.compLinearMap_apply] using
    PostedFieldDegreeAllocations.original (n:=n) (k:=k)
      (fun j ν => T j (fun i => (PowerSeries.coeff (ν i) Z) (v i)))
end
end IssuedBridge.PostedFieldSubstitution
