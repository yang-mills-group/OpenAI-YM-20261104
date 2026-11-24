import YM.Integration.WilsonFirstInheritedVacuumIncome

/-! One quoted allowance and spatial width for every vacuum coefficient required at
the first nonbare marked step, including its infinitely many zero angular ranks. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFirstInheritedVacuumRows
open Function Filter Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Winding
open scoped Classical BigOperators

theorem original {G : Gauge} (e : ℕ) (H E : Credit) (u : Gear G → ℝ) (hu : ∀ I, 0 < u I) :
    ∃ (c : Gear G → ℝ) (U : Credit), (∀ I, 0 < c I) ∧
      ∀ (Q : Realm G (e+1) E) (m : ℕ) (hm : Q.anchor ≤ m),
        let I := (Q.mint m hm).gear
        c I ≤ Q.cash H m → ∀ (n : Side) (a : ℕ), a ≤ e → ∀ l,
          Sight ((story Q.draws Q.paid (m+1) m).1 n a l)
            (actionW Q.draws Q.paid (m+1) m a l) (c I)⁻¹ (Q.cash U m) := by
  classical
  let T := Fin (e+1) × Fin (e+2)
  choose c U positive row using fun t : T =>
    WilsonFirstInheritedVacuumIncome.original (i:=t.1.val) (r:=t.2.val)
      (Nat.lt_succ_iff.mp t.1.isLt) H E u hu
  let cap (I : Gear G) := 1 + ∑ t : T, |c t I|
  have high (I : Gear G) (t : T) : c t I ≤ cap I := by
    calc
      c t I ≤ |c t I| := le_abs_self _
      _ ≤ ∑ b : T, |c b I| := Finset.single_le_sum (fun b _ => abs_nonneg (c b I)) (Finset.mem_univ t)
      _ ≤ cap I := le_add_of_nonneg_left zero_le_one
  let B : Credit := ⟨∑ t : T, (U t).d, 1 + ∑ t : T, (U t).x,
    le_add_of_nonneg_right (Finset.sum_nonneg fun t _ => zero_le_one.trans (U t).good)⟩
  have rent (t : T) (y : ℝ) (hy : 1 ≤ y) : (U t).buy y ≤ B.buy y := by
    apply mul_le_mul _ _ (pow_nonneg (zero_le_one.trans hy) _) (zero_le_one.trans B.good)
    · exact (Finset.single_le_sum (fun t _ => zero_le_one.trans (U t).good)
        (Finset.mem_univ t)).trans (le_add_of_nonneg_left zero_le_one)
    · apply pow_le_pow_right₀ hy
      change (U t).d ≤ ∑ b : T, (U b).d
      exact Finset.single_le_sum (fun b _ => Nat.zero_le (U b).d) (Finset.mem_univ t)
  refine ⟨cap,B, (fun I => by dsimp [cap]; positivity), ?_⟩
  intro Q m hm I paid n a ha l
  have nonneg : 0 ≤ Q.cash B m := zero_le_one.trans (B.purchase (Q.depth _ hm))
  cases l with
  | zero => exact (WilsonFiniteCommonKineticReset.quiet _ _ (Nat.lt_succ_self m) n a _).more nonneg
  | succ k =>
    by_cases hk : k < e+2
    · let t : T := (⟨a,Nat.lt_succ_of_le ha⟩, ⟨k,hk⟩)
      have h := row t Q m hm ((high I t).trans paid) n
      exact (h.mono (inv_anti₀ (positive t I) (high I t))).more (rent t _ (Q.depth _ hm))
    · have original := (old Q.draws Q.paid Q.hG Q.green (m+1) m (Nat.le_succ _)).basis n
      have finiteZero := original.lamp a (k+1) (by omega)
      have coverZero := post_end (A:=Q.draws) Q.hG Q.green (Nat.le_succ m) a (k+1) (by omega)
      rw [finiteZero, coverZero]
      exact (Sight.zero (n:=n) (r:=k+1) (α:=Hooks G) (V:=ℝ) (s:=(cap I)⁻¹)).more nonneg

end YM.Integration.WilsonFirstInheritedVacuumRows
