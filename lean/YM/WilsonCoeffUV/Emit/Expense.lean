import YM.WilsonCoeffUV.Emit.Rerender
import YM.Pert.Asymptotics.RawAxis
-- Numeric use of z and geometry costs. No scale TAIL bridge for actual remainders.
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Physical
open RG Function Filter Lattice Source Power Laurent Wilson Blue FreeResolvent Work.F08
open Precision Next.Foundations Input Supply WilsonCoeffLease
open Embroider Soil Cosmos Bank Bank.Mosaic Polestar Ticket
open Mer Patrol Wheel Wheel.Flooring Wheel.Cadenza
open Pert.Asymptotics
open scoped Topology BigOperators
variable {G:Gauge}{W:Prepaid0 G}{P:Funds0 G}{K:KernelChoices}{C:Family G}{A:Levels G}
variable (T U: Credit)

lemma stamp_lim (A:Levels G)(h:G.Simple):Tendsto (zz A) atTop atTop:= tendsto_atTop_add_const_left _ _ (Real.tendsto_log_atTop.comp (YM.Multi.Wage.log_tend h A))
lemma clock_dom (A:Levels G)(m:ℕ) : 1 ≤ A.clock.monitor m:= Real.one_le_exp (sq_nonneg _)
lemma time_change (A:Levels G)(i:ℕ): A.clock.monitor i = Real.exp ((zz A i-1)^2):= by simp [zz,Calendar.monitor]

lemma polynomial_decreasing (T:Credit): Tendsto (fun x:ℝ=> T.buy x/Real.exp (x-1)) atTop (𝓝 0):=by
  have he : Tendsto (fun x:ℝ=> T.x * (x^T.d * Real.exp (-x))* Real.exp 1) atTop (𝓝 0):=by
    simpa using ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero T.d).const_mul T.x).mul_const (Real.exp 1)
  apply he.congr; intro x; simp only [Credit.buy,Real.exp_sub,Real.exp_neg,div_eq_mul_inv,mul_inv,inv_inv]; ring

lemma absorbed (T:Credit)(d:ℝ)(hp:d>0): ∀ᶠ x:ℝ in atTop,T.buy x ≤ d*Real.exp (x-1):=
  (Filter.Tendsto.eventually_le_const hp (polynomial_decreasing T)).mono fun _ h=> (div_le_iff₀ (Real.exp_pos _)).mp h

section geom

lemma cone (T:Credit) (A:Levels G)(g:G.Simple)(η:ℝ)(p:η>0):∀ᶠ k:ℕ in atTop, T.buy (zz A k) ≤ A.clock.monitor k ^ η:=by
  have hu:0<T.x:= zero_lt_one.trans_le T.good
  let a := (4*(|Real.log T.x|+T.d:ℝ)+1)/η
  have ht x (hz:2≤x)(hk:a≤x): T.buy x≤ Real.exp ((x-1)^2*η):=by
    unfold a at hk; rw [div_le_iff₀ p] at hk
    have hp : Real.log T.x+T.d*Real.log x ≤ (x-1)^2*η:=by
       have H : η*x^2 ≤4* ((x-1)^2*η):=by
          have Hv : x^2 ≤ 4*(x-1)^2:=by nlinarith
          nlinarith only [p,Hv]
       have he : Real.log T.x ≤ |Real.log T.x| *x:=(le_abs_self _).trans (le_mul_of_one_le_right (by positivity) (by linarith))
       have hx:= Real.log_le_sub_one_of_pos (show 0<x by linarith)
       have hh:= mul_le_mul_of_nonneg_left hk (show 0≤x by linarith)
       nlinarith [Nat.cast_nonneg (α:=ℝ) T.d]
    apply (Real.log_le_iff_le_exp (by unfold Credit.buy; positivity)).mp
    simpa [Credit.buy,Real.log_mul hu.ne' (show x^T.d≠0 by positivity),Real.log_pow] using hp
  filter_upwards [ (stamp_lim A g).eventually_ge_atTop a,(stamp_lim A g).eventually_ge_atTop 2] with i hi he
  rw [time_change A,←Real.exp_mul]; exact ht (zz A i) he hi

lemma loop_petite (A: Levels G)(η:ℝ)(p:0<η): ∀ᶠ i:ℕ in atTop, A.clock.loopCap i≤2* A.clock.monitor i^η:=by
  have hp:Tendsto (fun i=> (A.clock.J i:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp A.fits.deep
  have h:Tendsto (fun i=> (A.clock.J i:ℝ)⁻¹) atTop (𝓝 0):= tendsto_inv_atTop_zero.comp hp
  filter_upwards [h.eventually_le_const p] with i hi; exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (clock_dom A i) (le_trans (A.fits.thetaRange i).2 hi)) (by norm_num)

/-- Expense in `against_Kin` (Rerender.lean). This geometry expense bound by powers of monitor comes
without *bounding loopCap itself by a polynomial in zz*, and is even
sub-ϖ (no inference about χ-curved actual constructors). -/
theorem retaining_expense (g:G.Simple) (A:Levels G)(T U:Credit)(η:ℝ)(p:0<η):
    ∀ᶠ m:ℕ in atTop, T.buy (zz A m)+ U.buy (zz A m)* A.clock.loopCap m ≤ 3*A.clock.monitor m^η:=by
  filter_upwards [cone T A g η p,cone U A g (η/2) (half_pos p),loop_petite A (η/2) (half_pos p)] with m t u w
  let M:= A.clock.monitor m; let x:ℝ:=M^(η/2); have h:0<M:= zero_lt_one.trans_le (clock_dom A m)
  have hp0:0≤x:=by unfold x; positivity
  calc
     _ ≤ M^η+x*(2*x) := add_le_add t (mul_le_mul u w (PhysicalNext.Repeat.Pane.coverBill ..).1 hp0)
     _ = _:=by
       have hx:M^η=x*x:=by unfold x; rw [← Real.rpow_add h]; congr 1; ring
       change M^η+_=3*M^η; rw [hx]; ring

/-- Includes exponential-of-poly z bills. The expense is *numeric*, across
entire actual β band. Use only around a scale where the producer admits
that order (no propagation rule here). -/
theorem exp_at_band (T:Credit)(A:Levels G)(g:G.Simple)(η:ℝ)(p:0<η) : ∀ᶠ m:ℕ in atTop,
    ∀ β:ℝ,β≥ A.clock.hatBeta m/2 → (Real.exp (T.buy (zz A m))) ≤ ((Real.sqrt β)⁻¹)^(-η):=by
  filter_upwards [ (stamp_lim A g).eventually (absorbed T (η/4) (by positivity)), (YM.Multi.Wage.log_tend g A).eventually_ge_atTop (2*Real.log 2)] with m hm hM
  intro β hβ; let H:=A.clock.hatBeta m; have h0:0<H:=zero_lt_one.trans (A.fits.delayed m)
  have hb:= (show A.clock.hatBeta m/2>0 from half_pos h0).trans_le hβ
  have hu : Real.exp (zz A m-1)=Real.log H:= by unfold H; simp [zz,Real.exp_log (Real.log_pos (A.fits.delayed m))]
  have ht: T.buy (zz A m) ≤ (η/2)*Real.log β:=by
    rw [hu] at hm
    change 2*Real.log 2≤ Real.log H at hM
    have hp:= Real.log_le_log (show 0<H/2 from half_pos h0) hβ; rw [Real.log_div h0.ne' (by norm_num)] at hp; nlinarith
  rw [Real.rpow_def_of_pos (by positivity), Real.log_inv,Real.log_sqrt hb.le]; exact Real.exp_le_exp.mpr (by linarith)

include C in
lemma exp_billed (h:G.Simple)(p:C.Makes)(T:Credit)(η:ℝ)(q:0<η): ∀ᶠ m:ℕ in atTop,
    ∀ N i:ℕ,m≤N → let A:=C.path.levels; Real.exp (T.buy (zz A m)) ≤ (regulatorRun C N i m)^(-η) :=
  (exp_at_band T _ h η q).mono (fun m H N i hm=>H _ (p.wilson.represents N i m hm).band.1)
end geom
end YM.WilsonCoeffUV.Physical
