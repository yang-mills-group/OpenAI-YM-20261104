import YM.Integration.WilsonDepositedFreshMarkedInput
import YM.Integration.WilsonInheritedWindingTransport

/-! Uniform cover income for a registered point source installed two dates above a
reporter, propagated through the true older vacuum and joined by a fresh source. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonTwoBirthCoverIncome
open Function Finset Lattice Wilson RG Source Labels Marker WilsonCoeffUV
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding IndependentSourcePathFamily
open FundedMarkedPathSelection WilsonLimitConstruction
open scoped Classical BigOperators
variable {G : Gauge} {ι : Type} [DecidableEq ι] [Fintype ι] {D k : ι → ℕ}
variable {I U : ι → Type} [∀ z, Fintype (I z)] [∀ z, Fintype (U z)] {e m : ℕ}

abbrev amount (Q : Realm G (e+1) Credit.leanC) (K : ι → ℕ) (b : ℝ) : ℝ :=
  FundedInheritedMarkedInput.fee (D:=D) (k:=k) Q K (m+1) (m+2) b + b

/-- The price is fixed before the older top, the complete output geometry, and the
period. Its source bills are measured on the canonical width-four chart. -/
theorem original (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m)
    (cloze : Cloze D k Q Credit.leanC) (K : ι → ℕ) (b : ℝ) (hb : 0 ≤ b)
    (one₁ : (Q.mint (m+1) (hm.trans (Nat.le_succ _))).σ ≤ 1)
    (one₂ : (Q.mint (m+2) (hm.trans (by omega))).σ ≤ 1)
    (X : ∀ z, I z → Seed G (D z)) (Y : ∀ z, U z → Seed G (D z))
    (hX : ∀ z j, (X z j).rank ≤ k z + (X z j).head)
    (hY : ∀ z j, (Y z j).rank ≤ k z + (Y z j).head)
    (payX : bill X k e 4 ≤ b) (payY : bill Y k e 4 ≤ b) :
    let A := amount (m:=m) (D:=D) (k:=k) Q K b
    0 ≤ A ∧ ∀ N, m+2 ≤ N → ∀ (old : Finset ι)
      (cells : (ι → Cover) → ι → Site (loose Q.draws m).L),
      ∃ T : Input Q hm univ k D A, T.offsets = cells ∧
        (∀ y S, S ⊆ old → T.familyAt y S =
          Gears Q.draws Q.paid K k N (m+2) (m+1) (independent X)
            (chartIn (loose Q.draws m) y (cells y)) S) ∧
        (∀ y z, z ∉ old → T.familyAt y {z} =
          single Y z (chartIn (loose Q.draws m) y (cells y) z)) := by
  classical
  let w := fun _ : Gear G => (1 : ℝ)
  have hw : ∀ M, 0 < w M := fun _ => zero_lt_one
  have hi : m+1 ≤ m+2 := Nat.le_succ _
  have oldFee := FundedInheritedMarkedInput.charge (D:=D) (k:=k) Q hm hi K b hb
  have freshFee : OriginalIssuedMarkedRows.fee (k:=k) Y Q hm w = bill Y k e 4 := by
    change bill Y k e (4 * max 1 (Q.mint (m+1) _).σ) = bill Y k e 4
    rw [max_eq_left one₁, mul_one]
  have raw (y : ι → Cover) := preblock X (k:=k) y univ e (show (0:ℝ)<4 by norm_num) hX
  have blank : Uniform Q (independent X) (m+2) (hm.trans (by omega)) b := by
    intro y S a ha r
    have source := (raw y).2.2.2 S (subset_univ _) a ha r
    have width : (Q.mint (m+2) (hm.trans (by omega))).σ ≤ steep 4 := by
      simpa only [show steep (4:ℝ) = 1 by unfold steep; norm_num] using one₂
    exact (source.shave width).more (pow_le_pow_left₀ (raw y).1 payX S.card)
  refine ⟨add_nonneg oldFee hb, ?_⟩
  intro N top old cells
  let T₀ := FundedInheritedMarkedInput.input Q hm hi top cloze K (independent X)
    (OriginalCoverReanchoring.deposited X hX).1 hb blank univ cells
  let T₁ := WilsonDepositedFreshMarkedInput.posted T₀ oldFee old Y w hw hY
  have hY₀ := (OriginalIssuedMarkedRows.enters Y Q hm w hw univ T₀.offsets hY).1
  let T : Input Q hm univ k D (amount (m:=m) (D:=D) (k:=k) Q K b) := {
    familyAt := T₁.familyAt, offsets := T₁.offsets, empty := T₁.empty, degree := T₁.degree
    price := fun y S hS a ha r => (T₁.price y S hS a ha r).more
      (pow_le_pow_left₀ (add_nonneg oldFee hY₀) (add_le_add (le_refl _) (freshFee.le.trans payY)) S.card) }
  exact ⟨T, rfl, fun y _ hS => WilsonDepositedFreshMarkedInput.deposited T₀ oldFee old Y w hw hY y hS,
    fun y z hz => WilsonDepositedFreshMarkedInput.fresh T₀ oldFee old Y w hw hY y hz⟩
end YM.Integration.WilsonTwoBirthCoverIncome
end

