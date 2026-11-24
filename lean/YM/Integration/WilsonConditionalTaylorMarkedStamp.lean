import YM.Integration.WilsonConditionalTaylorMarkedWidths
import YM.Integration.WilsonConditionalTaylorBulkStamp

/-! The positive rooted strip survives the physical, varying input/output
clock factors at every order of the whole signed marked polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorMarkedStamp
open FormalBulk08
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F03 Work.F05 Work.F08 Flat Mesa Tree Bank Kemp Rift
open WilsonConditionalTaylorBulkStamp
open scoped Topology BigOperators Classical

theorem variableWeight {I : Type} {r : ℕ} {η b : ℝ} {w : Side→ℝ} {x : Biglot I}
    {T : Tile (Biglot I) r} {U : (n:Side)→ Tile (Tor n I) r}
    (h : Kalm η x T U) (hw : Tendsto w atTop (𝓝 b)) :
    Kalm η x (b • T) (fun n=>w n • U n) := by
  obtain ⟨point,C,price⟩:=h
  refine ⟨fun u=>hw.mul (point u),(|b|+1)*C,?_⟩
  have bound : ∀ᶠ n in atTop, abs (w n) < abs b + 1 := hw.abs.eventually (gt_mem_nhds (lt_add_one _))
  filter_upwards [price,bound] with n paid hn
  exact (paid.smul (w n)).mono (mul_le_mul_of_nonneg_right hn.le paid.1)

theorem action {G : Gauge} (W : Pot G) (V : (n:Side)→Pap (wire G n)) (x : edgeL G)
    {A B : PowerSeries ℝ} {a b : Side→PowerSeries ℝ} (p : Scalar A a) (q : Scalar B b)
    (e r : ℕ) (income : ∀ j≤e, ∃ s:ℝ, 0<s ∧ Kalm s x (W j r) (fun n=>rancho (V n) j r)) :
    ∃ η : ℝ,0<η ∧ Kalm η x (Wine.stamp A B W e r)
      (fun n=>rancho (Wine.canter (a n) (b n) _ (V n)) e r) := by
  let P:=fun j (_ : ℕ) s=>Kalm s x (W j r) (fun n=>rancho (V n) j r)
  have all: ∀ j ≤ e, ∀ k ≤ 0,∃ s:ℝ,0<s ∧ P j k s:=fun j hj _ _=>income j hj
  obtain ⟨s,pos,fee⟩:=WilsonConditionalTaylorMarkedWidths.finite e 0 P all (fun _ _ _ _=>WilsonConditionalTaylorMarkedWidths.narrower)
  refine ⟨s,pos,?_⟩
  simp only [Wine.stamp_book,Wine.stamp]
  exact kalm_many _ fun j hj=>variableWeight (fee j (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj) 0 le_rfl) (weight p q e j r)

theorem shape {G : Gauge} {l : ℕ} (V : Pot G) (A B : PowerSeries ℝ) (due : Young V l) : Young (Wine.stamp A B V) l :=by
  intro e r hr
  by_contra bad
  apply hr
  unfold Wine.stamp
  refine Finset.sum_eq_zero fun j hj=>?_
  have hj':j≤e:=by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj
  have z:V j r=0:=by by_contra live;apply bad;exact (due j r live).trans (Nat.add_le_add_left hj' _)
  rw [z,smul_zero]

theorem finiteShape {I : Type} [Fintype I] {l : ℕ} (V : Pap I) (A B : PowerSeries ℝ) (due : Young (rancho V) l) :
    Young (rancho (Wine.canter A B I V)) l :=by
  intro e r hr
  by_contra bad
  apply hr
  rw [Wine.stamp_book]
  refine Finset.sum_eq_zero fun j hj=>?_
  have hj':j≤e:=by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj
  have z:rancho V j r=0:=by by_contra live;apply bad;exact (due j r live).trans (Nat.add_le_add_left hj' _)
  rw [z,smul_zero]

end YM.Integration.WilsonConditionalTaylorMarkedStamp
end

