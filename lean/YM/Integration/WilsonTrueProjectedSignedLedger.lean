import YM.Integration.WilsonTrueProjectedMeasuredScale

/-! Finite signed accumulation of the actual measured primary feeds. Each
change is transported once from its receiving frame to the reporting frame. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedSignedLedger
open Function Filter Finset Lattice Wilson RG Labels Source Trace.Physical Trace.Physical.GermGraph
open Extra.Histories PhysicalNext Repeat Legato
open scoped Classical Topology Matrix.Norms.Frobenius
variable {G : Gauge} (C : Family G) {d m j N p stop : ℕ}
local notation "σ" => (C.labels.level d).coeffSize
local notation "X" => measuring C d N p

def carry (H : C.Makes) (hm : Opened C d m p) (hj : Opened C d j p)
    (hmN : m ≤ N) (hjN : j ≤ N) : C.label d →ₗ[ℂ] C.label d :=
  (fitting d N p m H hm hmN).toLinearMap.comp (fitting d N p j H hj hjN).symm.toLinearMap

theorem earned (H : C.Makes) (hm : Opened C d m p) (hj : Opened C d j p)
    (range : m ≤ j) (live : j ≤ N) (v : C.label d) :
    σ (carry C H hm hj (range.trans live) live v) ≤ 4*(C.S.a m/C.S.a j)^(d+1)*σ v := by
  let e := fitting d N p j H hj live
  have bill := WilsonTrueProjectedMeasuredScale.original C H hm hj range live (e.symm v)
  change _ ≤ 4*(C.S.a m/C.S.a j)^(d+1)*σ (e (e.symm v)) at bill
  change σ (X m (e.symm v)) ≤ _
  simpa only [e.apply_symm_apply] using bill

theorem difference (H : C.Makes) (hm : Opened C d m p) (hj : Opened C d j p)
    (hmN : m ≤ N) (hjN : j ≤ N) (y z : C.label d) :
    carry C H hm hj hmN hjN (X j y-X j z) = X m y-X m z := by
  let g := fitting d N p m H hm hmN
  let e := fitting d N p j H hj hjN
  change g (e.symm (e y-e z))=g y-g z
  have pulled : e.symm (e y-e z) = y-z :=
    (congrArg e.symm (map_sub e y z).symm).trans (e.symm_apply_apply _)
  exact (congrArg g pulled).trans (map_sub g y z)

theorem signed (H : C.Makes) (hm : Opened C d m p) (range : m ≤ stop) (live : stop ≤ N)
    (ready : ∀ i ≥ m, i < stop → Opened C d i p) (path : ℕ → C.label d) (fee : ℕ → ℝ)
    (paid : ∀ i ≥ m, i < stop → σ (X i (path (i+1)) - X i (path i)) ≤ fee i) :
    let date := fun t : Fin (stop-m) => m+t.val
    let word := fun t : Fin (stop-m) =>
      let i := date t
      have hi : i < stop := by dsimp [i,date]; omega
      carry C H hm (ready i (Nat.le_add_right m t.val) hi) (range.trans live) (hi.le.trans live)
        (X i (path (i+1))-X i (path i))
    X m (path stop) - X m (path m) = ∑ t, word t ∧
    σ (X m (path stop) - X m (path m)) ≤
      ∑ t : Fin (stop-m), 4*(C.S.a m/C.S.a (date t))^(d+1)*fee (date t) := by
  intro date word
  have endDate : m+(stop-m)=stop := by omega
  have closed : (∑ t,word t) = X m (path stop)-X m (path m) := by
    calc
      _ = ∑ t : Fin (stop-m), (X m (path (date t+1))-X m (path (date t))) := by
        apply Finset.sum_congr rfl
        intro t _
        apply difference
      _ = ∑ t ∈ Finset.range (stop-m), (X m (path (m+t+1))-X m (path (m+t))) :=
        Fin.sum_univ_eq_sum_range (fun t => X m (path (m+t+1))-X m (path (m+t))) _
      _ = _ := by
        simpa only [←Nat.add_assoc,endDate,Nat.add_zero] using
          sum_range_sub (fun t => X m (path (m+t))) (stop-m)
  refine ⟨closed.symm,?_⟩
  rw [←closed]
  apply (Size.finite _ Finset.univ word).trans
  apply Finset.sum_le_sum
  intro t _
  have lo : m ≤ date t := Nat.le_add_right m t.val
  have hi : date t < stop := by dsimp [date]; omega
  have scale : 0 ≤ 4*(C.S.a m/C.S.a (date t))^(d+1) :=
    mul_nonneg (by norm_num) (pow_nonneg (div_nonneg (C.S.a_pos _).le (C.S.a_pos _).le) _)
  exact (earned C H hm (ready _ lo hi) lo (hi.le.trans live) _).trans
    (mul_le_mul_of_nonneg_left (paid _ lo hi) scale)

end YM.Integration.WilsonTrueProjectedSignedLedger
