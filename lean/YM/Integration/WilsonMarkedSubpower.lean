import YM.Integration.WilsonInitialOrdinaryPrice
import YM.Integration.WilsonPrescribedPacketTail
import YM.Integration.WilsonPreparedDualPrice

/-! Ordinary-event funding on the true zero-calibration initial Wilson inputs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedSubpower
open Filter Lattice Wilson RG Marker PhysicalNext.Repeat.Legato IterationFour
open LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Pert.Asymptotics MergeProof MergeProof.Accent IterationFour.Vacuum PhysicalNext.ThroughLaunch
open scoped Classical BigOperators Topology
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}

open MarkedPackets

/-- A fixed marked exponential is a finite polynomial in its genuine source geometry. -/
theorem polynomial (cap marks : ℕ) {a x : ℝ} (ha : 0≤a) (hx : 1≤x) (hax : a≤x) :
    uniformModelCost cap marks a ≤ ((marks+1:ℕ):ℝ)*(max 1 ((2:ℝ)^cap*(marks:ℝ)))^marks*x^marks := by
  let c := max 1 ((2:ℝ)^cap*(marks:ℝ))
  have hc : 1≤c := le_max_left ..
  have h0 : 0≤uniformReadCost cap marks a := mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) ha)
  have hr : uniformReadCost cap marks a ≤ c*x := by
    unfold uniformReadCost
    rw [←mul_assoc]
    exact mul_le_mul (le_max_right ..) hax ha (zero_le_one.trans hc)
  have hu := one_le_mul_of_one_le_of_one_le hc hx
  unfold uniformModelCost
  calc _ ≤ ∑ _i ∈ Finset.range (marks+1),(c*x)^marks := by
         apply Finset.sum_le_sum
         intro i hi
         exact ((div_le_self (pow_nonneg h0 _) (by exact_mod_cast Nat.factorial_pos i)).trans
           (pow_le_pow_left₀ h0 hr _)).trans (pow_le_pow_right₀ hu (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
       _ = _ := by simp [c,mul_pow,mul_assoc]

omit [DecidableEq V] [Fintype V] in
/-- Any positive inverse power of the true fine coupling pays the entire marked
polynomial before the cutoff and torus period are chosen. -/
theorem paid (R : Run G) (hG : G.Simple) (J : Request V) (A : NumericSchedule R.family J) (K : NumericPrices A)
    (cap marks : ℕ) (tau : ℝ) (htau : 0<tau) : ∃ c : ℝ, 0<c ∧ ∀ᶠ m : ℕ in atTop,
      ∀ N p : ℕ,m<N → uniformModelCost cap marks (K.geometry m) ≤ c*regulatorRun R.family N p (m+1)^(-tau) := by
  let eps := tau / ((marks:ℝ)+1)
  have he : 0<eps := div_pos htau (by positivity)
  have eunit : eps*((marks:ℝ)+1)=tau := by unfold eps; field_simp
  obtain ⟨n,price⟩ := K.subpower eps he
  let c := ((marks+1:ℕ):ℝ)*(max 1 ((2:ℝ)^cap*(marks:ℝ)))^marks
  have hc : 0<c := mul_pos (by positivity) (pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left ..)) _)
  refine ⟨c,hc,?_⟩
  filter_upwards [eventually_ge_atTop n,ActualRunAdjacentCoupling.eventually_ratio R hG,
    Currency.g_small hG R.makes (1/2) (by norm_num)] with m hn ratio small
  intro N p hm
  let f := regulatorRun R.family N p (m+1)
  let g := regulatorRun R.family N p m
  have hf : 0<f := Currency.g_pos R.makes _ _ _ hm
  have hg : 0<g := Currency.g_pos R.makes _ _ _ hm.le
  have gap : f≤2*g := (div_le_iff₀ hg).mp (ratio N p hm).2
  have hgmax : g≤1/2 := (small N p hm.le).le
  have hfmax : f≤1 := by linarith
  have hu : 1≤f^(-eps) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hf hfmax (neg_nonpos.mpr he.le)
  have hcost := polynomial cap marks (K.geometry_nonnegative m) hu (price m hn N p hm)
  have last : (f^(-eps))^marks ≤ f^(-tau) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hf.le]
    apply Real.rpow_le_rpow_of_exponent_ge hf hfmax
    nlinarith only [eunit,he]
  exact hcost.trans (mul_le_mul_of_nonneg_left last hc.le)

end YM.Integration.WilsonMarkedSubpower
