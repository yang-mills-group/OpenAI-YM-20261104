import YM.Integration.WilsonPhysicalHistoryKioskRough
import YM.QuadraticLocal.Shelter.Pins

/-! Signed short-step re-expression of the full previously entered regular
painter at its original marker weights. The finite support of each
registered summand also gives exact agreement beyond its diameter. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryKioskDifference
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

private theorem signed (t : T) (U : Config G n) :
    raw.log t U-filed.log t U-residual.log t U=(Deck.soap d d₁ d₀ matched).log t U := by
  rw [Deck.order (x:=t) (U:=U) w pos d d₁ d₀ matched ha rawPaid filedPaid residualPaid]
  abel

include hA width in
theorem priced (s : R.Mode) (v u : V) (hv : v∈s.val) (hu : u∈s.val) (t : T) (U : Config G n) :
    Poly.toll w s * ‖(raw.log t U-filed.log t U-residual.log t U).part s‖ ≤
      Real.exp (-A*(separation (o v) (o u)/Push.GridApprox.Attach.leg B : ℕ))*
        (Deck.crewCost H A τ*(b+b₁+b₀)) := by
  have pay : (Deck.soap d d₁ d₀ matched).Budget w B A (Deck.crewCost H A τ*(b+b₁+b₀)) := by
    simpa using Deck.paying w pos d d₁ d₀ matched ha hA width rawPaid filedPaid residualPaid 1 le_rfl
  rw [signed d d₁ d₀ matched w pos ha rawPaid filedPaid residualPaid]
  exact WilsonPhysicalHistoryKioskRough.separated _ pos hA pay s v u hv hu t U

theorem outside (s : R.Mode) (v u : V) (hv : v∈s.val) (hu : u∈s.val)
    (apart : H+H<separation (o v) (o u)) (t : T) (U : Config G n) :
    (raw.log t U-filed.log t U-residual.log t U).part s=0 := by
  let M := Deck.soap d d₁ d₀ matched
  have covers (c : E) : (coverNumber B (D.barrier o H c) : ℝ) ≤ coverNumber B (univ : Support n) := by
    exact_mod_cast Corona.cover_mono (Finset.subset_univ _) B
  have pay : M.Budget w B 0 (Deck.crewCost H 0 (coverNumber B (univ : Support n))*(b+b₁+b₀)) := by
    simpa [M] using Deck.paying w pos d d₁ d₀ matched ha (show (0:ℝ)≤0 from le_rfl)
      covers rawPaid filedPaid residualPaid 1 le_rfl
  rw [signed d d₁ d₀ matched w pos ha rawPaid filedPaid residualPaid]
  change (∑' c, M.soap t c U).part s=0
  rw [Poly.share (M.earnings pay pos le_rfl t U) s]
  calc
    _ = ∑' _ : E, (0:ℂ) := by
      apply tsum_congr
      intro c
      by_contra active
      have native := (M.cost t c).carry U s active
      have near (z : V) (hz : z∈s.val) : separation (D.center o c) (o z) ≤ H :=
        (Animals.neighbors_mem _ _ _).1 (native z hz)
      have dist := separation_triangle (o v) (D.center o c) (o u)
      rw [separation_comm (o v) (D.center o c)] at dist
      exact (Nat.not_lt_of_ge (dist.trans (Nat.add_le_add (near v hv) (near u hu)))) apart
    _ = 0 := tsum_zero

end YM.Integration.WilsonPhysicalHistoryKioskDifference
