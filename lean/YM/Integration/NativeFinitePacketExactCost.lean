import YM.Integration.NativeFinitePacketLaws
import YM.Integration.NativeFinitePacketPayment

/-! Exact finite accounting for the native padded packet constructor.
No factor depending on the number of rows is introduced, and no positivity
or nonzero-coupling assumption is needed for these algebraic identities. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeFinitePacketPayment
open Function Finset Lattice Wilson RG Marker
open LocalComparison Comparison.Density.RenderM
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V]
  {R : Census V} {D : V → ComparisonDensity.Address.Orbit} {count : ℕ}
  (mode : Fin count → R.Mode) (rank : Fin count → ℕ) (power : Fin count → ℤ)
  (T : (k : Fin count) → Token G n (fun v => (D v).Mood) (rank k))
  (hm : ∀ k, mode k ≠ R.quiet)
  (hg : ∀ k, 0 ≤ power k + (rank k : ℤ))

private theorem rank_at (i : ℕ) (hi : i < count) :
    (MarkedPackets.ofFin mode rank power T hm hg).rank i = rank ⟨i, hi⟩ := by
  change (if h : i < count then rank ⟨i, h⟩ else 0) = _
  exact dif_pos hi

private theorem token_at (i : ℕ) (hi : i < count) :
    (MarkedPackets.ofFin mode rank power T hm hg).packet i =
      some (cast (congrArg (fun q => Token G n (fun v => (D v).Mood) q)
        (rank_at mode rank power T hm hg i hi).symm) (T ⟨i, hi⟩)) := by
  change (if h : i < count then
    some (cast (congrArg (fun q => Token G n (fun v => (D v).Mood) q)
      (rank_at mode rank power T hm hg i h).symm) (T ⟨i, h⟩))
    else none) = _
  rw [dif_pos hi]

omit [DecidableEq V] in
private theorem cast_coin {a b : ℕ} (h : a = b)
    (t : Token G n (fun v => (D v).Mood) a) :
    (cast (congrArg (fun q => Token G n (fun v => (D v).Mood) q) h) t).coin =
      t.coin := by
  cases h
  rfl

omit [DecidableEq V] in
private theorem cast_fall {a b : ℕ} (h : a = b)
    (t : Token G n (fun v => (D v).Mood) a) :
    (cast (congrArg (fun q => Token G n (fun v => (D v).Mood) q) h) t).fall =
      t.fall := by
  cases h
  rfl

/-- Every original row has exactly its original mode, power, coin and path bill. -/
theorem ofFin_charge (w : V → ℝ) (g width : ℝ) (k : Fin count) :
    charge (MarkedPackets.ofFin mode rank power T hm hg) w g width k.val =
      Poly.toll w (mode k) * ‖(g : ℂ) ^ power k‖ *
        (T k).coin * Real.exp (width * (T k).fall) := by
  have hmode : (MarkedPackets.ofFin mode rank power T hm hg).mode k.val = mode k := by
    change (if h : k.val < count then mode ⟨k.val, h⟩ else R.quiet) = _
    exact dif_pos k.isLt
  have hpower : (MarkedPackets.ofFin mode rank power T hm hg).power k.val = power k := by
    change (if h : k.val < count then power ⟨k.val, h⟩ else 0) = _
    exact dif_pos k.isLt
  unfold charge
  rw [token_at mode rank power T hm hg k.val k.isLt, hmode, hpower]
  exact congrArg₂ (fun (coin : ℝ) (fall : ℕ) =>
     Poly.toll w (mode k) * ‖(g : ℂ) ^ power k‖ *
       coin * Real.exp (width * fall))
     (cast_coin (D := D) (rank_at mode rank power T hm hg k.val k.isLt).symm
       (T ⟨k.val, k.isLt⟩))
     (cast_fall (D := D) (rank_at mode rank power T hm hg k.val k.isLt).symm
       (T ⟨k.val, k.isLt⟩))
 
/-- Exact total finite cost, counting each retained row once. -/
theorem totalCost_ofFin (w : V → ℝ) (g width : ℝ) :
    totalCost (MarkedPackets.ofFin mode rank power T hm hg) count w g width =
      ∑ k : Fin count, Poly.toll w (mode k) * ‖(g : ℂ) ^ power k‖ *
        (T k).coin * Real.exp (width * (T k).fall) := by
  unfold totalCost
  apply Finset.sum_bij (fun i hi => (⟨i, Finset.mem_range.mp hi⟩ : Fin count))
  · intro i hi
    exact Finset.mem_univ _
  · intro i hi j hj he
    exact congrArg Fin.val he
  · intro k hk
    exact ⟨k.val, Finset.mem_range.mpr k.isLt, rfl⟩
  · intro i hi
    exact ofFin_charge mode rank power T hm hg w g width
      ⟨i, Finset.mem_range.mp hi⟩

end YM.Integration.NativeFinitePacketPayment
end
