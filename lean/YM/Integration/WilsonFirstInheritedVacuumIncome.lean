import YM.Integration.WilsonFirstInheritedVacuum

/-! The bare Wilson step provides the two compared vacuum rows on every finite torus.
The measured reversion at that step has one enrolled numerical allowance, chosen
before the period and the date are supplied. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFirstInheritedVacuumIncome
open Function Filter Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Winding
open scoped Classical BigOperators

private theorem common {α : Type} [Fintype α] (U : α → Credit) :
    ∃ V : Credit, ∀ y : ℝ, 1 ≤ y → ∀ a, (U a).buy y ≤ V.buy y := by
  classical
  have finite (S : Finset α) :
      ∃ V : Credit, ∀ y : ℝ, 1 ≤ y → ∀ a ∈ S, (U a).buy y ≤ V.buy y := by
    induction S using Finset.induction_on with
    | empty => exact ⟨Credit.unit, by simp⟩
    | insert b S _ ih =>
      obtain ⟨V, bound⟩ := ih
      refine ⟨(U b).plus V, ?_⟩
      intro y hy a ha
      rcases Finset.mem_insert.mp ha with h | h
      · subst a
        exact Credit.thickens (T:=U b) V hy
      · exact (bound y hy a h).trans (Credit.thickened (V:=V) (U b) hy)
  obtain ⟨V, hV⟩ := finite Finset.univ
  exact ⟨V, fun y hy a => hV y hy a (Finset.mem_univ a)⟩

theorem original {G : Gauge} {e i r : ℕ} (hi : i ≤ e) (H E : Credit)
    (u : Gear G → ℝ) (hu : ∀ I, 0 < u I) :
    ∃ (c : Gear G → ℝ) (U : Credit), (∀ I, 0 < c I) ∧
      ∀ (Q : Realm G (e+1) E) (m : ℕ) (hm : Q.anchor ≤ m),
        let I := (Q.mint m hm).gear
        c I ≤ Q.cash H m → ∀ n : Side,
          Sight ((story Q.draws Q.paid (m+1) m).1 n i (r+1))
            (actionW Q.draws Q.paid (m+1) m i (r+1)) (c I)⁻¹ (Q.cash U m) := by
  classical
  obtain ⟨c, U, hc, filed⟩ := WilsonFirstInheritedVacuum.original (r:=r) hi H E u hu
  obtain ⟨B, hB⟩ := common U
  obtain ⟨d, hd⟩ := rimMoney G i (r+1) e hi
  choose A hA bound using hd
  let expense := (H.prodC ((costXV G e E).powC d)).prodC B
  refine ⟨fun I => max (c I) (A I), expense, fun I => lt_of_lt_of_le (hc I) (le_max_left ..), ?_⟩
  intro Q m hm I income n
  have paid := filed Q m hm ((le_max_left ..).trans income) n
  apply (paid.mono (inv_anti₀ (hc I) (le_max_left ..))).more
  let C := ReelTime Q (i:=e) le_rfl hm (Nat.lt_succ_self m) (le_refl (m+1)) (le_refl (m+1))
  have rim : rimJ C.P.moving i (r+1) ≤ Q.cash H m * C.x ^ d :=
    (bound I C).trans (mul_le_mul_of_nonneg_right ((le_max_right ..).trans income)
      (pow_nonneg (zero_le_one.trans C.rich) _))
  have low : WilsonFiniteCommonKineticReset.fee C.P.moving i (r+1)
      (WilsonFirstInheritedVacuum.rent Q m U) ≤ rimJ C.P.moving i (r+1) * Q.cash B m := by
    unfold WilsonFiniteCommonKineticReset.fee rimJ
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a ha
    have ai := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa only [WilsonFirstInheritedVacuum.rent, dif_pos ai] using
      hB _ (Q.depth _ hm) ⟨a,Nat.lt_succ_of_le ai⟩
  have funded := low.trans (mul_le_mul_of_nonneg_right rim
    (zero_le_one.trans (Credit.purchase B (Q.depth m hm))))
  have moving : C.P.moving = back (Kstar (freshet Q.draws Q.paid (m+1) m)) := rfl
  have price : C.x = Q.cash (costXV G e E) m := rfl
  rw [moving, price] at funded
  simpa only [expense, cash, Credit.products, Credit.power] using funded

end YM.Integration.WilsonFirstInheritedVacuumIncome
