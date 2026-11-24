import YM.Integration.WilsonReportExteriorTail
import YM.Next.RANK.Station

/-! The actual physical mark radii absorb the entire selected finite product
cost before any upper cutoff, torus, location or independent gauge spectator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportExteriorBudget
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi
open Next.Rank Next.Rank.Spindle OPE OPE.Yarn OPE.Strobe OPE.Strobe.Vista26
open PhysicalNext.Repeat.Legato MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open WilsonReportExteriorTail
open scoped BigOperators Classical
variable {G : Gauge} {C : Family G} {W r D} {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
private theorem absorb (hG : G.Simple) (hCost : Log.OnBudget C.path.levels)
    (d : V→ℕ) (t : ℕ) : ∀ᶠ k : ℕ in atTop, ∀ N p, ∀ v : (j:V)→C.label (d j),
    (∀ j,Spindle.paid C (d j) k N p (v j)≤ C.path.levels.clock.hatBeta k^t) → ∀ s : Finset V,
    Real.exp (-2*((C.path.levels.budget k).B:ℝ))*price (k:=k) (N:=N) (p:=p) d v s ≤
      Real.exp (-((C.path.levels.budget k).B:ℝ)) := by
  let n := Fintype.card V
  let e := (t+1)*n+1
  have grow := Next.Rank.Station.hat_rate C.path.levels hG
  filter_upwards [grow.eventually_ge_atTop ((n:ℝ)*4^n),
    (Real.tendsto_log_atTop.comp grow).eventually_ge_atTop (e:ℝ)] with k large height N p v labels s
  let b := C.path.levels.clock.hatBeta k
  have hb : 1≤b := (C.path.levels.fits.delayed k).le
  have hb0 : 0≤b := zero_le_one.trans hb
  let c (j : V) := (C.path.levels.params k).columns*Spindle.paid C (d j) k N p (v j)
  have cn (j) : 0≤c j := mul_nonneg (zero_le_one.trans (C.path.levels.params k).columns_ge)
    (paid_pos C (d j) k N p (v j))
  have cap (j) : c j ≤ b^(t+1) := by
    have hh := mul_le_mul (hCost.present k) (labels j) (paid_pos C (d j) k N p (v j)) hb0
    change c j ≤ b*b^t at hh
    simpa only [pow_succ,mul_comm b (b^t)] using hh
  have cards : s.card ≤ n := card_le_univ _
  have mult : (s.card:ℝ)*4^s.card ≤ b :=
    (mul_le_mul (by exact_mod_cast cards : (s.card:ℝ)≤(n:ℝ))
      (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤4) cards) (by positivity) (Nat.cast_nonneg _)).trans large
  have prod : (∏ j ∈ s,c j) ≤ b^((t+1)*n) := calc
    _ ≤ ∏ _ ∈ s,b^(t+1) := prod_le_prod (fun j _ => cn j) (fun j _ => cap j)
    _ = (b^(t+1))^s.card := prod_const _
    _ ≤ (b^(t+1))^n := pow_le_pow_right₀ (one_le_pow₀ hb) cards
    _ = _ := (pow_mul ..).symm
  have pay : price (k:=k) (N:=N) (p:=p) d v s ≤ b^e :=
    (mul_le_mul mult prod (prod_nonneg (fun j _ => cn j)) hb0).trans_eq (by dsimp only [e]; rw [pow_succ,mul_comm])
  let B := ((C.path.levels.budget k).B:ℝ)
  have hp : 0<b := zero_lt_one.trans_le hb
  have bound : b^e ≤ Real.exp B := by
    apply (Real.log_le_iff_le_exp (pow_pos hp _)).mp
    rw [Real.log_pow]
    have hℓ := Real.log_nonneg hb
    change (e:ℝ) ≤ Real.log b at height
    exact (mul_le_mul_of_nonneg_right height hℓ).trans
      ((sq (Real.log b)).ge.trans (Nat.le_ceil _))
  exact (mul_le_mul_of_nonneg_left (pay.trans bound) (Real.exp_nonneg (-2*B))).trans_eq
    (by rw [← Real.exp_add]; congr 1; ring)

/-- Every earlier marked coarse truncation, tested with the actual gauge
spectator, has a uniform exp(-B_k) price after summing every finite slot cost. -/
theorem purchased (hG : G.Simple) (hC : C.Makes) (book : Log.OnBudget C.path.levels)
    (citizen : Citizen C W r D) (d : V→ℕ) (t : ℕ) : ∀ᶠ k : ℕ in atTop,
    ∀ N p, k<N → ∀ x : V→Site (C.side k p), ∀ v : (j:V)→C.label (d j),
    (∀ j,Spindle.paid C (d j) k N p (v j)≤C.path.levels.clock.hatBeta k^t) → ∀ s : Finset V,
    ∀ X : Config G (C.side k p)→ℂ, Integrable X (Therm.scene C.path N p k) →
    let μ := Therm.scene C.path N p k
    ‖(∫ U, X U*fineJob (regularPack (N:=N) d x v) s U ∂μ)-
      (∫ U, X U*fineJob (ScenePack (N:=N) d x v) s U ∂μ)‖ ≤
      (∫ U, ‖X U‖ ∂μ)*Real.exp (-((C.path.levels.budget k).B:ℝ)) := by
  filter_upwards [absorb hG book d t,
    eventually_all.mpr (fun j : V => eventually_ge_atTop (C.ref (d j)))] with k tariff refs
  intro N p hk x v funds s X hX
  have pay := (WilsonReportExteriorTail.integrated hG hC citizen hk d refs
    (C.path.levels.budget k).B x v s X hX).2.2
  exact pay.trans (mul_le_mul_of_nonneg_left (tariff N p v funds s)
    (integral_nonneg (fun _ => norm_nonneg _)))

end YM.Integration.WilsonReportExteriorBudget
end

