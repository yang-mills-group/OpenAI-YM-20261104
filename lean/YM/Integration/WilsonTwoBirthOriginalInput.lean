import YM.Integration.WilsonTwoBirthMarkedWinding

/-! The first two births on one funded original Wilson realm, with both
actual raw source placements and all the independently generated old modes. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonTwoBirthOriginalInput
open Function Finset Lattice Wilson RG Source Labels Marker WilsonCoeffUV
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding IndependentSourcePathFamily
open FundedMarkedPathSelection WilsonLimitConstruction
open scoped Classical BigOperators
variable {G : Gauge} {ι : Type} [DecidableEq ι] [Fintype ι] {D k : ι → ℕ}
variable {I U : ι → Type} [∀ i, Fintype (I i)] [∀ i, Fintype (U i)] {e m : ℕ}

/-- A single funded table on the issued realm retains the deposited Gears
and adds the registered bare singleton. Its measured finite–cover receipt
holds for the full before-test input, at each original reporting period. -/
theorem original (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m)
    (cloze : Cloze D k Q Credit.leanC) (K : ι → ℕ)
    (X : ∀ i, I i → Seed G (D i)) (Y : ∀ i, U i → Seed G (D i))
    (hX : ∀ i b, (X i b).rank ≤ k i + (X i b).head)
    (hY : ∀ i b, (Y i b).rank ≤ k i + (Y i b).head)
    (w : Gear G → ℝ) (hw : ∀ B, 0 < w B) (old : Finset ι)
    (cells : (ι → Cover) → ι → Site (loose Q.draws m).L) :
    ∃ (A : ℝ) (T : Input Q hm univ k D A), 0 ≤ A ∧ T.offsets = cells ∧
      (∀ y S, S ⊆ old → T.familyAt y S =
        Gears Q.draws Q.paid K k (m+2) (m+2) (m+1) (independent X)
          (chartIn (loose Q.draws m) y (cells y)) S) ∧
      (∀ y i, i ∉ old → T.familyAt y {i} = single Y i (chartIn (loose Q.draws m) y (cells y) i)) ∧
      ∃ σ B : ℝ, 0 < σ ∧ 1 ≤ B ∧ ∀ (n : Side) (y : ι → Cover) (S : Finset ι) (a : ℕ), a ≤ e →
        ∀ r, MarkU (chartIn (loose Q.draws m) y (cells y)) S
          ((T.familyAt y S).1 (n*(loose Q.draws m).L) a r) ((T.familyAt y S).2 a r) σ (B^S.card) := by
  have hi : m+1 ≤ m+2 := Nat.le_succ _
  let T₀ := FundedInheritedMarkedInput.actual Q hm hi (N:=m+2) le_rfl cloze K X hX univ cells
  have base := FundedInheritedMarkedInput.first (k:=k) Q X ((hm.trans (Nat.le_succ m)).trans hi) hX
  have ca := FundedInheritedMarkedInput.charge (D:=D) (k:=k) Q hm hi K _ base.1
  let T := WilsonDepositedFreshMarkedInput.posted T₀ ca old Y w hw hY
  have cy := (OriginalIssuedMarkedRows.enters Y Q hm w hw univ T₀.offsets hY).1
  refine ⟨_, T, add_nonneg ca cy, rfl, ?_, ?_, ?_⟩
  · intro y S hS
    exact WilsonDepositedFreshMarkedInput.deposited T₀ ca old Y w hw hY y hS
  · intro y i hi'
    exact WilsonDepositedFreshMarkedInput.fresh T₀ ca old Y w hw hY y hi'
  · exact WilsonTwoBirthMarkedWinding.paired Q hm K X Y hX hY w hw old T₀ ca (fun _ => rfl)

end YM.Integration.WilsonTwoBirthOriginalInput
end
