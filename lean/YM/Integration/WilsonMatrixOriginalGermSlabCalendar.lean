import YM.Integration.ActualRunRatioGrowth
import YM.RG01.Slack

/-! The original clock supplies an increasing number of UV transitions
whose combined mesh ratio costs at most the registered temperature.
The length is elected before either the cutoff or the period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermSlabCalendar
open Filter Lattice RG PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G)
local notation:max "β" i:arg => R.alloy.B.a.clock.hatBeta i

private theorem heat {f:ℕ→ℝ} {m:ℕ} (each:∀i ≥ m,f (i+1) ≤ 2*f i) (n:ℕ):
    f (m+n) ≤ (2:ℝ)^n*f m:=by
  induction n with
  | zero=>simp
  | succ n ih=>
    calc f (m+n+1) ≤ 2*f (m+n):=each _ (by omega)
         _  ≤  2*(2^n*f m):=mul_le_mul_of_nonneg_left ih (by norm_num)
         _ = _:=by rw [pow_succ];ring

private theorem ratio (S:Schedule) (m n:ℕ) (x:ℝ) (nonneg:0 ≤ x)
    (each:∀i<n,((S.block (m+i)).val:ℝ) ≤ x):S.a m/S.a (m+n) ≤ x^n:=by
  induction n with
  | zero=>simp [(S.a_pos m).ne']
  | succ n ih=>
    have step:=each n (by omega)
    have prev:=ih (fun i hi=>each i (by omega))
    have one:S.a m/S.a (m+(n+1))=S.a m/S.a (m+n)*((S.block (m+n)).val:ℝ):=by
      rw [show m+(n+1)=m+n+1 by omega,S.a_step,div_div_eq_mul_div]
      ring
    rw [one,pow_succ]
    exact mul_le_mul prev step (Nat.cast_nonneg _) (pow_nonneg nonneg _)

def Short (m k:ℕ):Prop:=∀N:ℕ,m ≤ N→N ≤ m+k→
  R.family.S.a m/R.family.S.a N ≤ β m ∧ β N ≤ (β m)^2

theorem fixed (simple:G.Simple) (n:ℕ):∀ᶠ m:ℕ in atTop,Short R m n:=by
  let A:=R.alloy.B.a
  obtain ⟨t,fast⟩:=eventually_atTop.mp (RG01.Physical.nextHat simple A)
  obtain ⟨d,depth⟩:=eventually_atTop.mp (A.fits.deep.eventually_ge_atTop (2*n))
  filter_upwards [eventually_ge_atTop t,eventually_ge_atTop d,(WardBin.bell A simple).eventually_ge_atTop ((2:ℝ)^(n+1))] with m mt md large
  have positive:0 ≤ β m:=zero_le_one.trans (A.fits.delayed m).le
  have range (i:ℕ) (hi:i ≤ n+1): β (m+i) ≤ (β m)^2:=by
    have one:=heat (m:=m) (fun j hj=>fast j (mt.trans hj)) i
    apply one.trans
    rw [sq]
    exact mul_le_mul_of_nonneg_right ((pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hi).trans large) positive
  let blocks:=fun i:Fin (n+1)=>(R.family.S.block (m+i.val)).val
  obtain ⟨j,-,high⟩:=Finset.exists_max_image Finset.univ blocks Finset.univ_nonempty
  let M:ℝ:=blocks j
  have mp:1 ≤ M:=by
    change (1:ℝ) ≤ ((R.family.S.block (m+j.val)).val:ℝ)
    exact_mod_cast (show (1:ℕ) ≤ (R.family.S.block (m+j.val)).val from (R.family.S.block (m+j.val)).property)
  have honor:M^(2*n+1) ≤ β ((m+j.val)+1):=ActualRunRatioGrowth.ratio_power_le R simple (m+j.val) (2*n)
    (depth (m+j.val) (by omega))
  have bound:M^n ≤ β m:=by
    apply (sq_le_sq₀ (pow_nonneg (zero_le_one.trans mp) _) positive).mp
    rw [←pow_mul,mul_comm n 2]
    apply (pow_le_pow_right₀ mp (Nat.le_succ _)).trans
    exact honor.trans (range (j.val+1) (by omega))
  intro N lower upper
  let i:=N-m
  have eq:N=m+i:=by dsimp [i];omega
  have small:i ≤ n:=by dsimp [i];omega
  rw [eq]
  refine ⟨?_,range i (by omega)⟩
  apply (ratio R.family.S m i M (zero_le_one.trans mp) ?_).trans ((pow_le_pow_right₀ mp small).trans bound)
  intro h hh
  have compare:(R.family.S.block (m+h)).val ≤ blocks j:=high (⟨h,by omega⟩:Fin (n+1)) (Finset.mem_univ _)
  change ((R.family.S.block (m+h)).val:ℝ) ≤ (blocks j:ℝ)
  exact_mod_cast compare

theorem growing (simple:G.Simple):∃H:ℕ→ℕ,Tendsto H atTop atTop ∧ ∀ᶠm:ℕ in atTop,Short R m (H m):=by
  choose t ht using fun n=>eventually_atTop.mp (fixed R simple n)
  let H:=fun m=>Nat.findGreatest (fun n=>t n ≤ m) m
  refine ⟨H,tendsto_atTop.2 (fun n=>?_),?_⟩
  · filter_upwards [eventually_ge_atTop n,eventually_ge_atTop (t n)] with m mn paid
    exact Nat.le_findGreatest mn paid
  · filter_upwards [eventually_ge_atTop (t 0)] with m paid
    exact ht (H m) m (Nat.findGreatest_spec (P:=fun i=>t i ≤ m) (Nat.zero_le m) paid)

end YM.Integration.WilsonMatrixOriginalGermSlabCalendar
