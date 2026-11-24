import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedFinitePinCorrelation
namespace IssuedBridge.PostedFieldDegreeAllocations
open YM.XSpace.Normalize Finset
open scoped Classical BigOperators
noncomputable section
variable {n k : ℕ}

private theorem total (a : Days n) : a ∈ tally k n ↔ a none + ∑ i, a (some i) = k := by
  simp [tally, Finset.mem_finsuppAntidiag, Fintype.sum_option]

private def degree (a : Days n) (ha : a ∈ tally k n) (i : Fin n) : Fin (k+1) :=
  ⟨a (some i), by
    have hsum := (total a).mp ha
    have hi := Finset.single_le_sum (f:=fun i => a (some i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega⟩

theorem original (G : ℕ → (Fin n → ℕ) → ℂ) :
    ∑ a ∈ tally k n, G (a none) (fun i => a (some i)) =
    ∑ v : Fin n → Fin (k+1), if (∑ i, (v i).val) ≤ k then G (k-∑ i, (v i).val) (fun i => (v i).val) else 0 := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun a ha => degree a ha)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hsum := (total a).mp ha
    change (∑ i, a (some i)) ≤ k
    omega
  · intro a ha b hb eq
    have hs (i : Fin n) : a (some i) = b (some i) := congrArg Fin.val (congrFun eq i)
    have hass := (total a).mp ha
    have hbss := (total b).mp hb
    ext i
    cases i with
    | none => simp_rw [hs] at hass; omega
    | some i => exact hs i
  · intro v hv
    have bound := (Finset.mem_filter.mp hv).2
    let f : Option (Fin n) → ℕ := Option.elim' (k - ∑ i, (v i).val) (fun i => (v i).val)
    let a : Days n := Finsupp.equivFunOnFinite.symm f
    have ha : a ∈ tally k n := by
      apply (total a).2
      exact Nat.sub_add_cancel bound
    refine ⟨a,ha,?_⟩
    funext i
    exact Fin.ext (show a (some i) = (v i).val from rfl)
  · intro a ha
    have hsum := (total a).mp ha
    change G (a none) _ = G (k-∑ i, a (some i)) _
    exact congrArg (fun t => G t (fun i => a (some i))) (by omega)
end
end IssuedBridge.PostedFieldDegreeAllocations
