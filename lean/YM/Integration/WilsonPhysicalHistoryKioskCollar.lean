import YM.Integration.WilsonPhysicalHistoryKioskDifference

/-! A rough re-expression carrying an occupied mark must see a physical
flag within twice its own registered radius of that original mark. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryKioskCollar
open Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums QuadraticLocal QuadraticLocal.Shelter
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {V T I J K E : Type} [DecidableEq V]
  {p : BudgetPoint} {o : V → Site n} {R : Census V} {H B : ℕ}
  {raw : Lamps T I G p o R} {filed : Lamps T J G p o R} {residual : Lamps T K G p o R}
  {D : Terrain E R} {α β γ : E → Type}
  [∀ i, Fintype (α i)] [∀ i, Fintype (β i)] [∀ i, Fintype (γ i)]
  (d : Deck raw D H α) (d₁ : Deck filed D H β) (d₀ : Deck residual D H γ)
  (matched : ∀ c t U, Healthy p.threshold (D.barrier o H c) U →
    d.white c t U = d₁.white c t U + d₀.white c t U)
  (w : V → ℝ) (pos : ∀ v, 0<w v) {a A τ b b₁ b₀ : ℝ}
  (ha : 0≤a) (hA : 0≤A) (width : ∀ c, (coverNumber B (D.barrier o H c) : ℝ) ≤ τ)
  (rawPaid : raw.Paid w B a b) (filedPaid : filed.Paid w B a b₁)
  (residualPaid : residual.Paid w B a b₀)

include d d₁ d₀ matched pos ha rawPaid filedPaid residualPaid

theorem healthy (s : R.Mode) (v : V) (occupied : v∈s.val) (t : T) (U : Config G n)
    (cold : Healthy p.threshold (Animals.neighbors (H+H) (o v)) U) :
    (raw.log t U - filed.log t U - residual.log t U).part s = 0 := by
  let M := Deck.soap d d₁ d₀ matched
  have covers (c : E) : (coverNumber B (D.barrier o H c) : ℝ) ≤ coverNumber B (univ : Support n) := by
    exact_mod_cast Corona.cover_mono (Finset.subset_univ _) B
  have charge : M.Budget w B 0 (Deck.crewCost H 0 (coverNumber B (univ : Support n))*(b+b₁+b₀)) := by
    simpa [M] using Deck.paying w pos d d₁ d₀ matched ha (show (0:ℝ)≤0 from le_rfl)
      covers rawPaid filedPaid residualPaid 1 le_rfl
  have signed : raw.log t U - filed.log t U - residual.log t U = M.log t U := by
    rw [Deck.order (x:=t) (U:=U) w pos d d₁ d₀ matched ha rawPaid filedPaid residualPaid]
    dsimp only [M]
    abel
  rw [signed]
  change (∑' c, M.soap t c U).part s = 0
  rw [Poly.share (M.earnings charge pos le_rfl t U) s]
  calc
    _ = ∑' _ : E, (0:ℂ) := by
      apply tsum_congr
      intro c
      by_contra moved
      have center : separation (D.center o c) (o v) ≤ H :=
        (Animals.neighbors_mem ..).1 ((M.cost t c).carry U s moved v occupied)
      have within : D.barrier o H c ⊆ Animals.neighbors (H+H) (o v) := by
        intro y hy
        apply (Animals.neighbors_mem ..).2
        have dist := separation_triangle (o v) (D.center o c) y
        have fromRoot : separation (o v) (D.center o c) ≤ H := by
          rw [separation_comm]; exact center
        exact dist.trans (Nat.add_le_add fromRoot ((Animals.neighbors_mem ..).1 hy))
      have localCold : Healthy p.threshold (M.place c).val U := cold.mono_left within
      apply M.clean t c U _ localCold
      intro zero
      exact moved (by rw [zero]; rfl)
    _ = 0 := tsum_zero

end YM.Integration.WilsonPhysicalHistoryKioskCollar
