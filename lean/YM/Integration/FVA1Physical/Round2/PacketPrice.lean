import YM.Integration.FVA1Physical.Round2.CoordinatePackets
import YM.Integration.FVA1Physical.Round2.PhysicalRectangle

/-! Every packet of the exact sweep has a genuinely admissible rectangle,
including its already-opened exterior background. The rooted price is fixed
before all sweeps, terminal fields and dropped coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Finset Lattice RG Push Push.Uniform MSbar MSbar.Lis MSbar.Whisk
open scoped Classical
variable {σ : Type} [Fintype σ]

omit [Fintype σ] in
theorem coordinateWalk_value (h : σ→ℝ) (L : List σ) (distinct : L.Nodup) (j : σ) :
    coordinateWalk h L j = if j∈L then h j else 0 := by
  induction L with
  | nil => simp [coordinateWalk]
  | cons i L ih =>
    have both := List.nodup_cons.mp distinct
    change (h i • bolt i + coordinateWalk h L) j = _
    rw [Pi.add_apply,ih both.2]
    by_cases same : j=i
    · subst j; simp [bolt,Pi.smul_apply,both.1]
    · simp [bolt,Pi.smul_apply,same]

theorem rectangleInside_fresh {w : ℝ} (hw : 0≤w) (h : σ→ℝ) (cap : ∀ i,|h i|≤w)
    (L : List σ) (distinct : L.Nodup) (x : Positions σ) (small : ‖x‖≤w)
    (fresh : ∀ i∈L,x i=0) : rectangleInside h (Metric.closedBall 0 w) L x := by
  induction L generalizing x with
  | nil => exact mem_closedBall_zero_iff.mpr small
  | cons i L ih =>
    have both := List.nodup_cons.mp distinct
    intro t ht
    apply ih both.2
    · apply (pi_norm_le_iff_of_nonneg hw).2
      intro j
      by_cases eq : j=i
      · subst j
        simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,fresh i (by simp),zero_add]
        rw [show bolt i i = 1 by simp [bolt],mul_one,Real.norm_eq_abs,abs_mul,abs_of_nonneg ht.1]
        exact (mul_le_of_le_one_left (abs_nonneg _) ht.2).trans (cap i)
      · simpa [bolt,Pi.single_apply,eq,Ne.symm eq] using (norm_le_pi_norm x j).trans small
    · intro j hj
      have ne : j≠i := fun E=>both.1 (E ▸ hj)
      simp [bolt,ne,fresh j (List.mem_cons_of_mem _ hj)]

theorem coordinate_packet_inside {w : ℝ} (hw : 0≤w) (h : σ→ℝ) (cap : ∀ i,|h i|≤w)
    (q : ℕ) (L : List σ) (distinct : L.Nodup) (p : List σ × List σ) (hp : p∈coordinatePackets q L) :
    rectangleInside h (Metric.closedBall 0 w) p.1 (coordinateWalk h p.2) := by
  have both := List.nodup_append.mp (distinct.sublist (coordinate_packet_shape q L p hp).2.2)
  apply rectangleInside_fresh hw h cap p.1 both.1
  · apply (pi_norm_le_iff_of_nonneg hw).2
    intro i
    rw [coordinateWalk_value h p.2 both.2.1]
    split
    · exact cap i
    · simpa using hw
  · intro i hi
    rw [coordinateWalk_value h p.2 both.2.1, if_neg (fun member=>both.2.2 i hi i member rfl)]

theorem RectangleLedger.sweep_price {n : Side} {site : σ → Site n} {a w B : ℝ} {s m : ℕ}
    {F : Positions σ → ℝ} (H : RectangleLedger site a s w (Metric.closedBall 0 w) F m B) (hw : 0≤w) :
    ∃ price : List σ→ℝ, (∀ i, Yarn m (fun l=>price (i::l)*Measuring.swipe site a s (i::l))≤B) ∧
      ∀ (q : ℕ) (L : List σ) (_ : L.Nodup) (p : List σ × List σ) (_ : p∈coordinatePackets q L),
        p.1.length=m+1 → ∀ h : σ→ℝ, (∀ i,|h i|≤w) →
          |rectangle h p.1 F (coordinateWalk h p.2)| ≤ price p.1.reverse := by
  obtain ⟨price,cost,row⟩ := H.covers
  refine ⟨price,row,?_⟩
  intro q L distinct p hp len h cap
  have inside := coordinate_packet_inside hw h cap q L distinct p hp
  have H₁ := (cost p.1.reverse (by simpa using len)).2 p.1.reverse.length h (coordinateWalk h p.2) cap
  have H₂ := H₁ (by rw [List.take_length,List.reverse_reverse]; exact inside)
  simpa only [mixedRectangle,List.take_length,List.reverse_reverse,List.drop_length,List.length_nil,pow_zero,mul_one,buoy,List.map_nil,roc] using H₂

end YM.Integration.FVA1Physical.Round2
