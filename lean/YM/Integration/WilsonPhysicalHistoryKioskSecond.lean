import YM.Integration.WilsonPhysicalHistoryKioskFirst
import YM.QuadraticLocal.Shelter.Pins
import YM.QuadraticLocal.Pry

/-! Reexpress the actual regular output of the first merger on its common
healthy supports. Its signed difference on each support is carried by the
second merger, with the original first-merger forced rows. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryKioskSecond
open Function Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums
open QuadraticLocal QuadraticLocal.Shelter
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {V T I J K E : Type} [DecidableEq V] [Fintype V] [Countable E]
  {P : Rep G n} {X : Activities G n} {o : V → Site n} {R : Census V} {H : ℕ}
  {fee final slack b b₁ b₀ t radius τ : ℝ}
  (middle : Hard T P.p X.forced X.K o R)
  (stage : Kiosk.Second P.p X P.activities fee final P.p.supportExponent slack)
  {raw : Lamps T I G P.p o R} {filed : Lamps T J G P.p o R} {residual : Lamps T K G P.p o R}
  {D : Terrain E R} {α β γ : E → Type}
  [∀ i, Fintype (α i)] [∀ i, Fintype (β i)] [∀ i, Fintype (γ i)]
  (d : Deck raw D H α) (d₁ : Deck filed D H β) (d₀ : Deck residual D H γ)
  (matched : ∀ i z U, Healthy P.p.threshold (D.barrier o H i) U →
    d.white i z U = d₁.white i z U + d₀.white i z U)
  (w : V → ℝ) (hw : ∀ v, 0 < w v) (ht : 0 ≤ t) (hr : 1 ≤ radius)
  (width : ∀ i, (coverNumber P.p.B (D.barrier o H i) : ℝ) ≤ τ)
  (rawPaid : raw.Paid w P.p.B t b) (filedPaid : filed.Paid w P.p.B t b₁)
  (residualPaid : residual.Paid w P.p.B t b₀)
  (fits : radius⁻¹ * (Deck.crewCost H (P.p.supportExponent+1) τ * (b+b₁+b₀)) ≤ slack)

abbrev returned := Gallery.mk (filed.join residual)
  (Kiosk.Second.canopy middle (Deck.soap d d₁ d₀ matched) stage)

include hw ht hr width rawPaid filedPaid residualPaid fits in
/-- The entire source passed to the first merger is recovered at each
configuration from the exhibited three decks and the true vacuum. -/
theorem restored (F : T → Config G n → Poly R)
    (income : middle.Paid w P.p.B (P.p.supportExponent+1) fee)
    (observed : ReadZone T P.p X middle F raw.log)
    (quiet : ∀ z U, (F z U).part R.quiet = (P.eval U : ℂ))
    (nonzero : ∀ U, P.eval U ≠ 0) :
    (returned middle stage d d₁ d₀ matched).E.Paid (Stoop.radius w radius) P.p.B t
        (radius⁻¹*b₁ + radius⁻¹*b₀) ∧
      (returned middle stage d d₁ d₀ matched).K.Paid (Stoop.radius w radius) P.p.B
        P.p.supportExponent final ∧
      ∀ z, F z = (returned middle stage d d₁ d₀ matched).density z := by
  let M := Deck.soap d d₁ d₀ matched
  have price := Deck.paying w hw d d₁ d₀ matched ht (show 0 ≤ P.p.supportExponent+1 by
    linarith [P.p.exponent_pos]) width rawPaid filedPaid residualPaid radius hr
  obtain ⟨g,hg,live⟩ := price.earned
  have paid : M.Budget (Stoop.radius w radius) P.p.B (P.p.supportExponent+1) slack :=
    ⟨g,hg,fun x => budget_loosen (live x) fits⟩
  have left := Stoop.tighten w filed hw hr filedPaid
  have right := Stoop.tighten w residual hw hr residualPaid
  have both := Lamps.joinPaid left right
  have hw' (v : V) : 0 < Stoop.radius w radius v := div_pos (hw v) (zero_lt_one.trans_le hr)
  have exactLog (z : T) (U : Config G n) : raw.log z U = (filed.join residual).log z U + M.log z U := by
    rw [Lamps.joinLog z U (filedPaid.sums ht hw z U) (residualPaid.sums ht hw z U)]
    exact Deck.order (x:=z) (U:=U) w hw d d₁ d₀ matched ht rawPaid filedPaid residualPaid
  obtain ⟨hard,read⟩ := Kiosk.Second.passes F raw.log middle M stage hw' P.p.exponent_pos.le
    (Stoop.leaves w middle hw hr income) paid observed (filed.join residual).log exactLog
    (fun z U => Lamps.quiet_of_hasSum _ _ (both.sums ht hw' z U))
  exact ⟨both,hard,upkeep F P (filed.join residual) _ both ht hw' read quiet nonzero⟩

end YM.Integration.WilsonPhysicalHistoryKioskSecond


