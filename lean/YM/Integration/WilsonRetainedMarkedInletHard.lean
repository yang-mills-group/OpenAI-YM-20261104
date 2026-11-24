import YM.Integration.WilsonRetainedMarkedInletRegular
import YM.QuadraticLocal.SameSlot

/-! One common envelope for the genuine old forced slots and all their signed marked entries. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000

noncomputable section
namespace YM.Integration.WilsonRetainedMarkedInletHard

open Function Finset Lattice Wilson RG Marker Overlay Ac QuadraticLocal Push.Corrected Push.AbsoluteSums
open scoped Classical Topology BigOperators

variable {G : Gauge} {n : Side} {V : Type*} [Fintype V] [DecidableEq V]
  {R : Census V} {P : Rep G n} (a : Bands R P) (h : a.Active)
  {w : V → ℝ} {u c d b δ κ : ℝ} (t : a.Radial w u c d b) (H : P.activities.Valid P.p δ κ)

omit [Fintype V] in
private theorem atom (j : R.Mode) {z : ℂ} {v : ℝ} (hz : ‖z‖ ≤ v) :
    Width.Covered (Poly.send j z) (Poly.send j (v:ℂ)) := by
  intro s
  by_cases hs : s=j <;> simp [Poly.part_send,hs,hz]

omit [Fintype V] in
private theorem plus {x y X Y : Poly R} (hx : Width.Covered x X) (hy : Width.Covered y Y) :
    Width.Covered (x+y) (X+Y) := by
  intro s
  rw [Poly.part_plus,Poly.part_plus,Complex.add_re,Complex.add_im]
  exact ⟨(norm_add_le _ _).trans (add_le_add (hx s).1 (hy s).1),by rw [(hx s).2,(hy s).2,add_zero]⟩

theorem purchased (e : ℝ) (he : e ≤ P.p.supportExponent) :
    (WilsonRetainedMarkedInlet.hard a h t H).Paid w P.p.B e (κ + Fintype.card V * (d*b)) := by
  classical
  obtain ⟨q,hq,reserve⟩ := H.boundK
  obtain ⟨f,hf,paid⟩ := t.hits
  let s (i : ℕ) := (P.activities.forced i).support
  let k (i : ℕ) := coverNumber P.p.B (s i)
  let bare (x : ℕ×ℕ) := Poly.toll w (a.marks x.1 x.2)*f x
  let total (x : ℕ×ℕ) := Poly.toll w (a.marks x.1 x.2)*P.p.mass (s x.1) (f x)
  have hb (x : ℕ×ℕ) : 0≤bare x := mul_nonneg (Poly.worth t.pure _).le (hf x.1 x.2).1
  have pool : SumBudget total (Fintype.card V*(d*b)) := Overlay.per_system
    (fun x => mul_nonneg (Poly.worth t.pure _).le
      ((hf x.1 x.2).1.trans (P.p.loMass _ _ (hf x.1 x.2).1)))
    (P:=fun x : ℕ×ℕ => a.marks x.1 x.2) (fun x => h.occurs x.1 x.2) paid
  obtain ⟨rows,outer⟩ := (summable_prod_of_nonneg (show 0≤total from pool.1)).mp pool.2.1
  have stripped (i : ℕ) : Summable (fun j => bare (i,j)) :=
    (rows i).of_nonneg_of_le (fun j => hb _) (fun j => mul_le_mul_of_nonneg_left
      (P.p.loMass _ _ (hf i j).1) (Poly.worth t.pure _).le)
  let added (i : ℕ) := ∑' j,total (i,j)
  have more : SumBudget added (Fintype.card V*(d*b)) :=
    ⟨fun i=>tsum_nonneg (fun j=>pool.1 (i,j)),outer,pool.2.1.tsum_prod.symm.trans_le pool.2.2⟩
  let group (i j : ℕ) := Poly.send (a.marks i j) (f (i,j):ℂ)
  have ledger (i : ℕ) : Summable (group i) ∧
      Poly.price w (∑' j,group i j) ≤ ∑' j,bare (i,j) :=
    Poly.budgeted t.pure (stripped i) (fun j => by
      simp [group,bare,Poly.solo,Real.norm_eq_abs,abs_of_nonneg (hf i j).1])
  let cap (i : ℕ) := Poly.send R.quiet (q i:ℂ) + ∑' j,group i j
  have bounds (i : ℕ) : Poly.price w (cap i) ≤ q i + ∑' j,bare (i,j) := by
    apply (Poly.addition t.pure _ _).trans
    simpa [Poly.solo,Poly.quiet_toll,Real.norm_eq_abs,abs_of_nonneg (hq i).1] using
      add_le_add_left (ledger i).2 (q i)
  refine ⟨cap,?_,?_⟩
  · intro i _ U
    change Width.Covered (a.each i U) (cap i)
    refine plus (atom R.quiet (by simpa using (hq i).2 U)) ?_
    exact SameSlot.coveredSum (fun j=>atom (a.marks i j) ((hf i j).2 U))
      ((a.baseBound h t H U).1 i) (ledger i).1
  · intro x
    apply budget_of_sum
    · intro i
      split
      next => exact mul_nonneg (Poly.nonnegative t.pure _) (Real.exp_pos _).le
      next => exact le_rfl
    · intro J
      have atSite (i : ℕ) : (if x∈s i then Poly.price w (cap i)*Real.exp (e*k i) else 0) ≤
          (if x∈s i then P.p.mass (s i) (q i) else 0) + added i := by
        by_cases hx : x∈s i
        · rw [if_pos hx,if_pos hx]
          have bound := mul_le_mul_of_nonneg_right (bounds i) (Real.exp_pos (e*k i)).le
          have re := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (k i)))
          have pos : 0≤q i+∑' j,bare (i,j) := add_nonneg (hq i).1 (tsum_nonneg fun j=>hb _)
          refine bound.trans ((mul_le_mul_of_nonneg_left re pos).trans_eq ?_)
          rw [add_mul]
          have eq : (∑' j,bare (i,j))*Real.exp (P.p.supportExponent*k i) = added i := by
            rw [←tsum_mul_right]
            apply tsum_congr
            intro j
            dsimp [bare,total,BudgetPoint.mass,k]
            ring
          rw [eq]
          simp [BudgetPoint.mass,k,mul_comm]
        · simpa [hx] using more.1 i
      calc
        _ ≤ ∑ i∈J,((if x∈s i then P.p.mass (s i) (q i) else 0)+added i) :=
          Finset.sum_le_sum fun i _ => atSite i
        _ ≤ _ := by
          rw [Finset.sum_add_distrib]
          exact add_le_add (budget_sum (reserve x) J) (budget_sum more J)

theorem original : (WilsonRetainedMarkedInlet.incoming a h t H).Pays w (P.p.supportExponent-1)
    (WilsonRetainedMarkedInletRegular.cost P.p * (Fintype.card V*c))
    (κ+Fintype.card V*(d*b)) :=
  ⟨WilsonRetainedMarkedInletRegular.purchased a h t,purchased a h t H _ (by linarith)⟩

end YM.Integration.WilsonRetainedMarkedInletHard

