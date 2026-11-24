import YM.Integration.WilsonPhysicalHistoryKioskSecond
import YM.QuadraticLocal.Shelter.Shadows

/-! Re-express the enrolled part of the first marked merger. The
complement keeps its actual old addresses, tests, health masks and
coupling factors. The second merger still acts on the full conditional. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryKioskSubset
open Function Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums QuadraticLocal QuadraticLocal.Shelter
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {V T I J K E M O : Type} [DecidableEq V] [Fintype V] [Countable E]
  {P : Rep G n} {X : Activities G n} {o : V → Site n} {R : Census V} {H : ℕ}
  {fee final slack b b₁ b₀ a radius τ : ℝ}
  (raw : Lamps T I G P.p o R) (choice : M⊕O ≃ I)
  (middle : Hard T P.p X.forced X.K o R) (stage : Kiosk.Second P.p X P.activities fee final P.p.supportExponent slack)
  {filed : Lamps T J G P.p o R} {residual : Lamps T K G P.p o R}
  {D : Terrain E R} {α β γ : E → Type}
  [∀ i, Fintype (α i)] [∀ i, Fintype (β i)] [∀ i, Fintype (γ i)]
  (d : Deck (raw.summon (fun i => choice (.inl i))) D H α)
  (d₁ : Deck filed D H β) (d₀ : Deck residual D H γ)
  (matched : ∀ i t U, Healthy P.p.threshold (D.barrier o H i) U →
    d.white i t U = d₁.white i t U + d₀.white i t U)
  (w : V → ℝ) (pos : ∀ v, 0 < w v) (ha : 0≤a) (hr : 1≤radius)
  (width : ∀ i, (coverNumber P.p.B (D.barrier o H i) : ℝ) ≤ τ)
  (rawPaid : raw.Paid w P.p.B a b) (filedPaid : filed.Paid w P.p.B a b₁)
  (residualPaid : residual.Paid w P.p.B a b₀)
  (fits : radius⁻¹*(Deck.crewCost H (P.p.supportExponent+1) τ*(b+b₁+b₀)) ≤ slack)

abbrev remainder := raw.summon (fun i => choice (.inr i))

abbrev output := Gallery.mk (filed.join (residual.join (remainder raw choice)))
  (Kiosk.Second.canopy middle (Deck.soap d d₁ d₀ matched) stage)

include pos ha hr width rawPaid filedPaid residualPaid fits in
theorem restored (F : T → Config G n → Poly R)
    (income : middle.Paid w P.p.B (P.p.supportExponent+1) fee)
    (observed : ReadZone T P.p X middle F raw.log)
    (quiet : ∀ t U, (F t U).part R.quiet = (P.eval U : ℂ))
    (nonzero : ∀ U, P.eval U ≠ 0) :
    let out := output raw choice middle stage d d₁ d₀ matched
    out.E.Paid (Stoop.radius w radius) P.p.B a
      (radius⁻¹*b₁ + (radius⁻¹*b₀ + radius⁻¹*b)) ∧
    out.K.Paid (Stoop.radius w radius) P.p.B P.p.supportExponent final ∧
    (∀ t U, raw.log t U = out.E.log t U + (Deck.soap d d₁ d₀ matched).log t U) ∧
    ∀ t, F t=out.density t := by
  let L := raw.summon (fun i => choice (.inl i))
  let O₀ := remainder raw choice
  let shift := Deck.soap d d₁ d₀ matched
  have near : L.Paid w P.p.B a b := raw.summonPaid w _ (choice.injective.comp Sum.inl_injective) rawPaid
  have old : O₀.Paid w P.p.B a b := raw.summonPaid w _ (choice.injective.comp Sum.inr_injective) rawPaid
  have h₁ := Stoop.tighten w filed pos hr filedPaid
  have h₀ := Stoop.tighten w residual pos hr residualPaid
  have ho := Stoop.tighten w O₀ pos hr old
  have both := Lamps.joinPaid h₁ (Lamps.joinPaid h₀ ho)
  have positive (v : V) : 0 < Stoop.radius w radius v := div_pos (pos v) (zero_lt_one.trans_le hr)
  have pre := Deck.paying w pos d d₁ d₀ matched ha (show 0≤P.p.supportExponent+1 by
    linarith [P.p.exponent_pos]) width near filedPaid residualPaid radius hr
  obtain ⟨g,hg,rent⟩ := pre.earned
  have paid : shift.Budget (Stoop.radius w radius) P.p.B (P.p.supportExponent+1) slack :=
    ⟨g,hg,fun x => budget_loosen (rent x) fits⟩
  have full (t : T) (U : Config G n) :
      raw.log t U = (filed.join (residual.join O₀)).log t U + shift.log t U := by
    have split := raw.separate choice (fun i => choice (.inl i)) (fun i => choice (.inr i))
      (fun _ => rfl) (fun _ => rfl) t U (rawPaid.sums ha pos t U)
    change raw.log t U=L.log t U+O₀.log t U at split
    rw [split,Deck.order (x:=t) (U:=U) w pos d d₁ d₀ matched ha near filedPaid residualPaid]
    rw [Lamps.joinLog t U (filedPaid.sums ha pos t U) ((Lamps.joinPaid residualPaid old).sums ha pos t U),
      Lamps.joinLog t U (residualPaid.sums ha pos t U) (old.sums ha pos t U)]
    dsimp only [shift]
    abel
  obtain ⟨hard,read⟩ := Kiosk.Second.passes F raw.log middle shift stage positive P.p.exponent_pos.le
    (Stoop.leaves w middle pos hr income) paid observed (filed.join (residual.join O₀)).log full
    (fun t U => Lamps.quiet_of_hasSum _ _ (both.sums ha positive t U))
  exact ⟨both,hard,full,upkeep F P _ _ both ha positive read quiet nonzero⟩

end YM.Integration.WilsonPhysicalHistoryKioskSubset
