import YM.Integration.WilsonTrueProjectedLocatedExpense
import YM.Integration.WilsonOriginalNullStock

/-! The numerical cost of all real primary transfers on a bounded corridor
depends only polynomially on its engineering length and its number of dates. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedLocatedTariff
open Filter MeasureTheory Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open QuadraticLocal QuadraticLocal.Advent AllOrder AllOrder.Floe AllOrder.Transit WheelP WilsonOriginalNullCorridor
open scoped Classical Topology BigOperators

open FormalBulk08 City Pose RemainderComparison ConnectedActivityE6
open WilsonTrueProjectedPointProgram WilsonTrueProjectedPointInverse
open WilsonTrueProjectedLocatedBasis WilsonTrueProjectedLocatedHistory
open WilsonPinnedWidthTransport WilsonTrueProjectedNaturalFee WilsonTrueProjectedCourse
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G)
local notation "C₀" => R.family


open WilsonTrueProjectedLocatedMerge WilsonTrueProjectedLocatedExpense
theorem chart {d N p b : ℕ} {W : Rep G ((C₀).side b p)} (home : Opened C₀ d b p)
    (budget : W.p=((C₀).path.rep N p b).p) (live : b ≤ N) :
    |tPrice ((C₀).labels.level d) (C₀).params W| ≤ 1 := by
  let L:=R.family.labels.level d
  have pp:W.p=plank R.family b:=budget.trans (R.makes.wilson.represents N p b live).vac
  have paid:tPrice L R.family.params W=invoice (C:=R.family) d b p:=by unfold tPrice;rw [pp]
  have z:0 ≤ tPrice L R.family.params W := mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    ((germ_close L R.family.params).choose_spec.1.le)) (Real.exp_pos _).le
  rw [abs_of_nonneg z,paid]
  have stok:1 ≤ stock R.family b:=(R.family.path.levels.params b).columns_ge
  have non:0 ≤ invoice (C:=R.family) d b p:=paid ▸ z
  have h:invoice (C:=R.family) d b p ≤ invoice (C:=R.family) d b p*stock R.family b:=
    (mul_one _).symm.le.trans (mul_le_mul_of_nonneg_left stok non)
  exact h.trans (home.small.le.trans (by norm_num))

theorem blocks {b n j : ℕ} (bj : b≤j) (inside : j<b+n) :
    factor C₀ j ≤ Real.exp (elapsed (C₀).S b (b+n)) := by
  have first: (R.family.S).scale b ≤ (R.family.S).scale j :=(OPE.scale_mono R.family.S).monotone bj
  have last: (R.family.S).scale (j+1) ≤ (R.family.S).scale (b+n) :=
    (OPE.scale_mono R.family.S).monotone (by omega)
  rw [Schedule.scale_succ] at last
  calc
    _ = Real.exp (Real.log (factor R.family j)) := (Real.exp_log (zero_lt_one.trans (factor_positive R.family j))).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by unfold elapsed;change _+Real.log (factor R.family j) ≤ _ at last;linarith)

theorem original : ∀ᶠ b : ℕ in atTop, ∀ d N p n,0<n → b+n≤N → ∀ η : ℝ,
    Opened C₀ d b p →
    roof R d N p b n η ≤ 6*(n+1)*Real.exp (((d:ℝ)+η+1)*elapsed (C₀).S b (b+n)) := by
  obtain ⟨u,facts⟩:=eventually_atTop.mp (factor_large R.family (1:ℝ) (by norm_num))
  filter_upwards [Filter.eventually_ge_atTop (u+1)] with b tail
  intro d N p n positive live η home
  let t:=elapsed R.family.S b (b+n)
  have bound (k:ℕ) (hk:u≤k):stock R.family (k+1) ≤ factor R.family k:=by
    have a:= (facts k hk).2
    rw [Real.rpow_one] at a
    have e:1 ≤ stock R.family (k+1):=(R.family.path.levels.params _).columns_ge
    linarith
  have each (i:ℕ) (hi:i∈Finset.range (n+1)) : stock R.family (b+i) ≤ Real.exp t := by
    cases i with
    | zero =>
      rw [add_zero]
      have h:stock R.family b ≤ factor R.family (b-1):=by
        convert bound (b-1) (by omega) using 2; omega
      have adj:=WilsonOriginalNullStock.adjacent R.family (b-1)
      rw [show b-1+1=b by omega] at adj
      exact h.trans (adj.trans (blocks R le_rfl (by omega)))
    | succ i =>
      have pre:stock R.family (b+i+1) ≤ factor R.family (b+i):=bound (b+i) (by omega)
      have edge:b+i<b+n:=by have:=Finset.mem_range.mp hi;omega
      exact pre.trans (blocks R (by omega) edge)
  have sum : (∑ i∈Finset.range (n+1),stock R.family (b+i)) ≤ (n+1)*Real.exp t := by
    simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_succ] using Finset.sum_le_sum each
  have price:=chart R (N:=N) home (W:=R.family.path.rep N p b) rfl (by omega)
  let W:=tPrice (R.family.labels.level d) R.family.params (R.family.path.rep N p b)
  have pos:0 ≤ ∑ i∈Finset.range (n+1),stock R.family (b+i):=Finset.sum_nonneg
    (fun i _=> zero_le_one.trans (R.family.path.levels.params _).columns_ge)
  change (2+|W|)*Real.exp (((d:ℝ)+η)*t)*(2*_) ≤ _
  calc
    _ ≤ (3*Real.exp (((d:ℝ)+η)*t))*(2*((n+1)*Real.exp t)) := mul_le_mul
      (mul_le_mul_of_nonneg_right (by change 2+|W| ≤ 3;linarith only [price]) (Real.exp_pos _).le)
      (mul_le_mul_of_nonneg_left sum (by norm_num)) (mul_nonneg (by norm_num) pos) (by positivity)
    _ = 6*(n+1)*Real.exp ((((d:ℝ)+η)+1)*t) := by
      rw [show ((((d:ℝ)+η)+1)*t)=((d:ℝ)+η)*t+t by ring,Real.exp_add];ring

end YM.Integration.WilsonTrueProjectedLocatedTariff
