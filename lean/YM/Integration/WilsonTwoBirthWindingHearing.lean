import YM.Integration.WilsonTwoBirthOriginalInput
import YM.Integration.WilsonFirstInheritedVacuumRows
import YM.Integration.WilsonFiniteIncomingWindingCurrent

/-! The finite-period signed answer at the first original block with an inherited source
and an independently placed fresh one, including the rebased vacuum. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section

namespace YM.Integration.WilsonTwoBirthWindingHearing
open Function Finset Lattice Wilson RG Source Labels Marker WilsonCoeffUV Precision Laurent
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Address
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Embroider WilsonCoeffUV.Winding
open IndependentSourcePathFamily FundedMarkedPathSelection WilsonLimitConstruction Work.F08
open scoped Classical BigOperators

variable {G : Gauge} {ι : Type} [DecidableEq ι] [Fintype ι] {D k : ι → ℕ}
variable {I U : ι → Type} [∀ z, Fintype (I z)] [∀ z, Fintype (U z)] {e i r : ℕ}
variable {J : Finset ι} {o : ι}

/-- The quiet credit is enrolled before the original realm. The second step keeps all
proper deposited modes and the true common change of kinetic variable. Its winding
price applies to a separate complex test and signed phase at every charged address. -/
theorem original (H : Credit) (menu : Gear G → ℝ) (hmenu : ∀ B, 0 < menu B) :
    ∃ (cap : Gear G → ℝ) (quiet : Credit), (∀ B, 0 < cap B) ∧
    ∀ (Q : Realm G (e+1) Credit.leanC) (m : ℕ) (hm : Q.anchor ≤ m),
      cap (Q.mint (m+1) (hm.trans (Nat.le_succ m))).gear ≤ Q.cash H (m+1) →
      ∀ (_cloze : Cloze D k Q Credit.leanC) (K : ι → ℕ)
        (X : ∀ z, I z → Seed G (D z)) (Y : ∀ z, U z → Seed G (D z)),
      (∀ z b, (X z b).rank ≤ k z + (X z b).head) →
      (∀ z b, (Y z b).rank ≤ k z + (Y z b).head) →
      ∀ (w : Gear G → ℝ), (∀ B, 0 < w B) → ∀ (old : Finset ι)
        (cells : (ι → Cover) → ι → Site (loose Q.draws m).L),
      o ∈ J → i ≤ e →
      ∃ (A : ℝ) (T : Input Q hm univ k D A), 0 ≤ A ∧ T.offsets = cells ∧
        (∀ y S, S ⊆ old → T.familyAt y S =
          Gears Q.draws Q.paid K k (m+2) (m+2) (m+1) (independent X)
            (chartIn (loose Q.draws m) y (cells y)) S) ∧
        (∀ y z, z ∉ old → T.familyAt y {z} = single Y z
          (chartIn (loose Q.draws m) y (cells y) z)) ∧
        ∃ (d : ℕ) (C B σ : ℝ), 0 ≤ C ∧ 1 ≤ B ∧ 0 < σ ∧
        ∀ (n : Side) (a : ℕ) (W : Credit) (u : ℝ), (σ/32/2/2)⁻¹ ≤ W.buy u → 1 ≤ u →
          let P := WilsonFiniteIncomingWindingCurrent.row Q.draws Q.paid m (m+2) n
            (fun z => T.familyAt (PeriodicMarkedWinding.roots n z o)) k J o i r
          let bound := C * (max 1 (Q.cash quiet (m+1)))^d * B^J.card *
            rimJ (ratioHigh Q.draws Q.paid (m+2) m) i r
          let fee := WilsonFiniteIncomingWindingCurrent.price G r a J o n σ bound W u
          PostMark J o r P (σ/256) fee a ∧
          ∀ (x : Cover) (v : Fence (Hooks G) J o r → SignedRootedWindingReadout.Tests D)
            (V : ℝ), 0 ≤ V → (∀ b, SignedRootedWindingReadout.amplitude J (v b) ≤ V) →
            ∀ ξ : Fence (Hooks G) J o r → ℂ, (∀ b, ‖ξ b‖ ≤ 1) →
            let f := fun b => ξ b * SignedRootedWindingReadout.read J (v b) (towerV J o r P x b)
            Summable f ∧ ‖∑' b, f b‖ ≤ V*fee := by
  classical
  obtain ⟨cap, quiet, positive, bare⟩ :=
    WilsonFirstInheritedVacuumRows.original e H Credit.leanC menu hmenu
  refine ⟨cap, quiet, positive, ?_⟩
  intro Q m hm paid cloze K X Y hX hY w hw old cells ho hi
  obtain ⟨A, T, hA, hcells, sold, fresh, w₀, B, hw₀, hB, before⟩ :=
    WilsonTwoBirthOriginalInput.original Q hm cloze K X Y hX hY w hw old cells
  let I₁ := (Q.mint (m+1) (hm.trans (Nat.le_succ m))).gear
  let s := min w₀ (cap I₁)⁻¹
  have hs : 0 < s := lt_min hw₀ (inv_pos.mpr (positive I₁))
  have short : (holt Q m hm s hs).s ≤ s := by
    have h : (holt Q m hm s hs).s ≤ s/32 := min_le_left _ _
    linarith
  obtain ⟨d,C,σ,hC,hσ,step⟩ :=
    WilsonFiniteIncomingWindingCurrent.original (D:=D) (k:=k) (r:=r) Q hm
      (subset_univ J) ho hi hs
  refine ⟨A, T, hA, hcells, sold, fresh, d, C, B, σ, hC, hB, hσ, ?_⟩
  intro n a W u hu hw'
  let y := fun z => PeriodicMarkedWinding.roots n z o
  apply step (m+2) (by omega) n (fun z => T.familyAt (y z)) (fun z => cells (y z))
    (fun z => T.empty (y z)) (fun z => T.degree (y z)) (max 1 (Q.cash quiet (m+1))) B
    (le_max_left _ _) (le_trans zero_le_one hB) _ _ a W u hu hw'
  · intro j hj l
    exact ((bare Q (m+1) (hm.trans (Nat.le_succ m)) paid _ j hj l).mono
      (short.trans (min_le_right _ _))).more (le_max_right _ _)
  · intro z S _ j hj l
    exact (before n (y z) S j hj l).mono (short.trans (min_le_left _ _))

end YM.Integration.WilsonTwoBirthWindingHearing
end

