import YM.Integration.WilsonCommonDepositedWinding
import YM.Integration.WilsonDepositedFreshMarkedInput
import YM.Integration.WilsonLimitConstruction.FundedInheritedMarkedInput

/-! Winding of the complete incoming source table on the next Wilson block
when a new curvature is registered beside the first deposited source. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonTwoBirthMarkedWinding
open Function Finset Lattice Wilson RG Source Labels Marker WilsonCoeffUV
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding IndependentSourcePathFamily
open FundedMarkedPathSelection WilsonLimitConstruction
open scoped Classical BigOperators
variable {G : Gauge} {ι : Type} [DecidableEq ι] [Fintype ι] {D k : ι → ℕ}
variable {I U : ι → Type} [∀ i, Fintype (I i)] [∀ i, Fintype (U i)] {e m : ℕ}

/-- Each proper old subword on this table is the unaltered finite and cover
entry of the first Wilson return. Each new raw singleton is the actual
registered source at its separate child cell. -/
theorem paired (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m)
    (K : ι → ℕ) (X : ∀ i, I i → Seed G (D i)) (Y : ∀ i, U i → Seed G (D i))
    (hX : ∀ i b, (X i b).rank ≤ k i + (X i b).head)
    (hY : ∀ i b, (Y i b).rank ≤ k i + (Y i b).head)
    (w : Gear G → ℝ) (hw : ∀ B, 0 < w B) (old : Finset ι)
    {A : ℝ} (T : Input Q hm univ k D A) (hA : 0 ≤ A)
    (history : ∀ y, T.familyAt y = Gears Q.draws Q.paid K k (m+2) (m+2) (m+1) (independent X)
      (chartIn (loose Q.draws m) y (T.offsets y))) :
    let table := WilsonDepositedFreshMarkedInput.posted T hA old Y w hw hY
    ∃ σ B : ℝ, 0 < σ ∧ 1 ≤ B ∧ ∀ (n : Side) (y : ι → Cover)
      (S : Finset ι) (a : ℕ), a ≤ e → ∀ r,
        MarkU (chartIn (loose Q.draws m) y (table.offsets y)) S
          ((table.familyAt y S).1 (n*(loose Q.draws m).L) a r) ((table.familyAt y S).2 a r)
          σ (B^S.card) := by
  classical
  intro table
  obtain ⟨s,A₀,hs,h₀,deposits⟩ := WilsonCommonDepositedWinding.retained Q
    (hm.trans (Nat.le_succ m)) X w hw hX K
  let t := (Q.mint (m+1) (by omega)).σ
  have ht : 0 < t := (Q.mint (m+1) (by omega)).width
  let I₀ := holt Q m hm t ht
  let A₁ := diamond G e (mass k Finset.univ) t * OriginalIssuedMarkedRows.fee (k:=k) Y Q hm w
  have hf := (preblock Y (k:=k) (fun _ => 0) univ e
    (w:=4 * max (w (Q.mint m hm).gear) t)
    (mul_pos (by norm_num) ((hw _).trans_le (le_max_left ..))) hY).1
  have h₁ : 0 ≤ A₁ := mul_nonneg (zero_le_one.trans (diamond_nn G ht)) hf
  refine ⟨min s I₀.s, max A₀ A₁, lt_min hs I₀.h, h₀.trans (le_max_left ..), ?_⟩
  intro n y S a he r
  by_cases kept : S ⊆ old
  · have same := WilsonDepositedFreshMarkedInput.deposited T hA old Y w hw hY y kept
    change table.familyAt y S = T.familyAt y S at same
    rw [same, history]
    exact ((deposits (n*(loose Q.draws m).L) (chartIn (loose Q.draws m) y (T.offsets y)) S a he r).mono
      (min_le_left ..)).more (pow_le_pow_left₀ (zero_le_one.trans h₀) (le_max_left ..) _)
  · let next := OriginalIssuedMarkedRows.input Y Q hm w hw univ T.offsets hY
    have same : table.familyAt y S = next.familyAt y S := if_neg kept
    rw [same]
    have fresh := WilsonRegisteredBareMarkedWinding.registered Q hm (Nat.lt_succ_self m) Y w hw univ
      T.offsets hY y n S (subset_univ S) a he r
    exact (fresh.mono (min_le_right ..)).more (pow_le_pow_left₀ h₁ (le_max_right ..) _)

end YM.Integration.WilsonTwoBirthMarkedWinding
end
