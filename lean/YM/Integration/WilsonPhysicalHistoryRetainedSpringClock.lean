import YM.Integration.WilsonPhysicalHistoryRetainedSpringMeasured
import YM.WilsonCoeffUV.Vacuum.UV.RatioLimit
import YM.WilsonCoeffUV.Emit.Expense

/-! The original absolute two-cutoff kinetic bill controls every coefficient
of the submitted finite clock before every cutoff and period. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Lattice Wilson RG Precision
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Bank.Ticket Comparison.RG02 Comparison.RG02.Assembly IterationFour
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Physical WilsonLimitConstruction PowerSeries
open scoped Topology BigOperators Classical
variable {G : Gauge}

private theorem pitch_credits (G : Gauge) (E r : ℕ) (hr : r≤E) :
    ∃ T : Credit, ∀ Q : Realm G E Credit.leanC,∀ j, Q.anchor≤j → ∀ N>j,∀ k≤r,
      |coeff k (pitch Q.draws Q.paid N j)| ≤ Q.cash T j := by
  induction r with
  | zero =>
    obtain ⟨T,cost⟩:=pitch_step G E Credit.leanC 0 (Nat.zero_le _)
    refine ⟨T,fun Q j hj N hN k hk=>?_⟩
    have eq : k=0:=by omega
    subst k
    exact (cost Q j hj (j+1) N N (Nat.lt_succ_self _) hN hN).main
  | succ r ih =>
    obtain ⟨T,old⟩:=ih (by omega)
    obtain ⟨S,new⟩:=pitch_step G E Credit.leanC (r+1) hr
    refine ⟨T.plus S,fun Q j hj N hN k hk=>?_⟩
    by_cases h:k≤r
    · exact (old Q j hj N hN k h).trans (Credit.thickens S (Q.depth _ hj))
    · have eq : k=r+1:=by omega
      subst k
      exact (new Q j hj (j+1) N N (Nat.lt_succ_self _) hN hN).main.trans (Credit.thickened T (Q.depth _ hj))

theorem cofinal_pitch (R : Run G) (simple : G.Simple) (v : ℕ→Gear G→ℝ)
    (rows : FundedMarkedCoverRows.prices v R.kit) (r : ℕ) :
    ∃ T : Credit, ∀ᶠ j : ℕ in atTop, ∀ N>j,∀ k≤r,
      |coeff k (pitch R.family.path.levels R.metals.O N j)| ≤ T.buy (zz R.family.path.levels j) := by
  obtain ⟨T,toll⟩:=pitch_credits G (r+1) r (Nat.le_succ _)
  refine ⟨T,?_⟩
  filter_upwards [FundedMarkedCoverRows.realm R simple v rows 0 (fun _=>0) (fun _=>1) (fun _=>Nat.zero_lt_succ _) r 0 0] with j data
  obtain ⟨Q,hA,hO,hy,atSite,_⟩:=data
  intro N later i hi
  have h:=toll Q j atSite.le N later i hi
  simpa only [hA,hO,Realm.cash,hy] using h

theorem poly_price (R : Run G) (N j r : ℕ) {g C : ℝ}
    (small : |g|≤1) (price : ∀ k≤r+2, |coeff k (pitch R.family.path.levels R.metals.O N j)| ≤ C) :
    |pitchPolynomial R N j r g| ≤ (r-2+1:ℕ)*C ∧ |pitchTail R N j r g| ≤ (r-2+1:ℕ)*C := by
  have cost (i h : ℕ) (hi : i<r-2+1) :
      |coeff (i+2) (pitch R.family.path.levels R.metals.O N j)*g^h| ≤ C := by
    rw [abs_mul,abs_pow]
    exact (mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) small)).trans (price _ (by omega))
  have nn : 0≤C:=(abs_nonneg _).trans (price 0 (Nat.zero_le _))
  constructor
  · apply (Finset.abs_sum_le_sum_abs ..).trans
    exact (Finset.sum_le_sum (fun i hi=>cost i i (Finset.mem_range.mp hi))).trans_eq (by simp)
  · apply (Finset.abs_sum_le_sum_abs ..).trans
    have hb (i : ℕ) (hi : i ∈ Finset.range (r-2+1)) :
        abs (if 2 ≤ i ∧ i % 2 = 0 then readSun (freshet R.family.path.levels R.metals.O N j (i+2) 2)*g^(i-2) else 0) ≤ C := by
      split
      · have t:=cost i (i-2) (Finset.mem_range.mp hi)
        change |coeff (i+2) (Kstar (freshet R.family.path.levels R.metals.O N j))*g^(i-2)| ≤ C at t
        simpa only [stellar_read] using t
      · simpa only [abs_zero] using nn
    exact (Finset.sum_le_sum hb).trans_eq (by simp)

end YM.Integration.OriginalMarkedRunAction
