import YM.Integration.WilsonPhysicalPositionWeakRoofDates
import YM.TraceExtension.Prom.Orion.Ramp

/-! Adjacent original dates on the single growing reporting ruler. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionWeakRoofCrossings
open Filter Set Lattice Wilson RG PhysicalNext.Repeat.Legato Next.Rank MergeProof.East
open WilsonPhysicalPositionWeakRoofClock WilsonPhysicalPositionWeakRoofRuler
open scoped Classical Topology
variable {G:Gauge}

private theorem reaches (g : ℕ → ℝ) (start : ℕ)
    (cut : ∀ k ≥ start, 2 * g (k+1) ≤ g k) {s : ℝ} (sp : 0 < s) :
    ∃ j, start < j ∧ g j ≤ s := by
  have decay (n : ℕ) : (2:ℝ)^n * g (start+1+n) ≤ g (start+1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      calc
        _ = (2:ℝ)^n * (2 * g (start+1+n+1)) := mul_assoc ..
        _ ≤ (2:ℝ)^n * g (start+1+n) :=
          mul_le_mul_of_nonneg_left (cut _ (by omega)) (by positivity)
        _ ≤ _ := ih
  obtain ⟨n,past⟩ := pow_unbounded_of_one_lt (g (start+1) / s) (by norm_num : 1 < (2:ℝ))
  refine ⟨start+1+n,by omega,?_⟩
  exact le_of_mul_le_mul_left ((decay n).trans ((div_lt_iff₀ sp).mp past).le)
    (by positivity : 0 < (2:ℝ)^n)

private theorem between (R : Run G) (simple : G.Simple) (b t : ℕ → ℝ) (pos : ∀ d, 0 ≤ b d)
    (width : ∀ᶠ k in atTop, topL R.family.path.levels k ≤ R.family.path.levels.clock.monitor k) :
    ∀ᶠ k : ℕ in atTop, ruler R b t k ≤
      Station.gap R.family.path.levels (dial R b t (k+1) + 1) (k+1) := by
  let A := R.family.path.levels
  filter_upwards [(tendsto_add_atTop_nat 1).eventually width,tide_mode A simple,
    (Station.hat_rate A simple).eventually_ge_atTop (Real.exp 1)] with k booked hmon hot
  have mom := WilsonStartup.Timing.hat_mono A (Gauge.slopeConstant_pos simple).le (Nat.le_succ k)
  have lp : 1 ≤ Real.log (A.clock.hatBeta k) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hot
  have hinc := Real.log_le_log (zero_lt_one.trans_le lp)
    (Real.log_le_log ((Real.exp_pos _).trans_le hot) mom)
  have hd : dial R b t k ≤ dial R b t (k+1) := (rate b t pos hinc).1
  have small : 0 ≤ dial R b t k := le_ciInf (fun d => add_nonneg (pos d) (le_max_left ..))
  have m1 : 1 ≤ A.clock.monitor (k+1) := Real.one_le_exp (sq_nonneg _)
  have hmag : Station.mag A (dial R b t k) k ≤ Station.mag A (dial R b t (k+1)) (k+1) :=
    (Real.rpow_le_rpow (Real.exp_pos _).le hmon small).trans
      (Real.rpow_le_rpow_of_exponent_le m1 hd)
  have block : ((A.S.block k).val:ℝ) ≤ A.clock.monitor (k+1) := by
    rw [←A.fits.sameFactor]
    exact (le_max_left ..).trans booked
  have space : A.S.a k = A.S.a (k+1)*((A.S.block k).val:ℝ) := by
    rw [A.S.a_step]
    exact (div_mul_cancel₀ _ (by exact_mod_cast (A.S.block k).property.ne')).symm
  have next : Station.mag A (dial R b t (k+1)+1) (k+1) =
      A.clock.monitor (k+1) * Station.mag A (dial R b t (k+1)) (k+1) := by
    unfold Station.mag
    rw [Real.rpow_add (show 0 < A.clock.monitor (k+1) from Real.exp_pos _),Real.rpow_one,mul_comm]
  change A.S.a k * Station.mag A (dial R b t k) k ≤
    A.S.a (k+1) * Station.mag A (dial R b t (k+1)+1) (k+1)
  rw [space,mul_assoc,next]
  exact mul_le_mul_of_nonneg_left (mul_le_mul block hmag (Station.mag_pos ..).le (Real.exp_pos _).le)
    (A.S.a_pos _).le

theorem original (R : Run G) (simple : G.Simple) (b t : ℕ → ℝ) (pos : ∀ d, 0 ≤ b d)
    (initial : b 0 ≤ t 0)
    (width : ∀ᶠ k in atTop, topL R.family.path.levels k ≤ R.family.path.levels.clock.monitor k)
    (before : ℕ) :
    ∃ start ≥ before, ∃ radius : ℝ, 0 < radius ∧ ∃ date : Ioc (0:ℝ) radius → ℕ,
      (∀ s, start < date s ∧ ruler R b t (date s) ≤ (s:ℝ) ∧
        (∀ j, start < j → ruler R b t j ≤ (s:ℝ) → date s ≤ j) ∧
        ∃ θ : ℝ, θ ∈ Icc 0 1 ∧ (s:ℝ) = Station.gap R.family.path.levels
          (dial R b t (date s)+θ) (date s)) ∧
      (∀ s u : Ioc (0:ℝ) radius, (s:ℝ) ≤ u → (u:ℝ) ≤ 2*(s:ℝ) →
        date u ≤ date s ∧ date s ≤ date u+1) := by
  let A := R.family.path.levels
  obtain ⟨k₀,step⟩ := eventually_atTop.mp ((between R simple b t pos width).and
    (halves R simple b t pos initial))
  let start := max k₀ before
  let radius := ruler R b t start
  have age : k₀ ≤ start := le_max_left ..
  have open_ (s : Ioc (0:ℝ) radius) : ∃ j, start < j ∧ ruler R b t j ≤ (s:ℝ) :=
    reaches _ start (fun j h => (step j (age.trans h)).2) s.2.1
  let date (s : Ioc (0:ℝ) radius) := Nat.find (open_ s)
  have specs (s : Ioc (0:ℝ) radius) : start < date s ∧ ruler R b t (date s) ≤ (s:ℝ) :=
    Nat.find_spec (open_ s)
  have first (s : Ioc (0:ℝ) radius) (j : ℕ) (h : start < j) (cost : ruler R b t j ≤ s) :
      date s ≤ j := Nat.find_min' _ ⟨h,cost⟩
  refine ⟨start,le_max_right ..,radius,Station.gap_pos ..,date,?_,?_⟩
  · intro s
    obtain ⟨late,reached⟩ := specs s
    refine ⟨late,reached,first s,gap_curve A _ (date s) s reached ?_⟩
    obtain ⟨j,eq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) late))
    change date s = j+1 at eq
    have prior : start ≤ j := by omega
    rw [eq]
    apply le_trans _ (step j (age.trans prior)).1
    rcases prior.eq_or_lt with old|inside
    · exact old ▸ s.2.2
    · exact le_of_lt (lt_of_not_ge (fun cost => (show j<date s by omega).not_ge (first s j inside cost)))
  · intro s u order close
    obtain ⟨ls,rs⟩ := specs s
    obtain ⟨lu,ru⟩ := specs u
    refine ⟨first u (date s) ls (rs.trans order),first s (date u+1) (by omega) ?_⟩
    have shrink := (step (date u) (age.trans lu.le)).2
    linarith only [shrink,ru,close]

end YM.Integration.WilsonPhysicalPositionWeakRoofCrossings
end
