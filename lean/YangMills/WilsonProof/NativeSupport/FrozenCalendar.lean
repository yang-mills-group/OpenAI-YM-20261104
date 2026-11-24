import YangMills.WilsonProof.NativeSupport.ReferenceOrder
import YM.Next.RANK.Station
import YM.Pert.Asymptotics.RawAxis

/-! Discharge the endpoint bill using the slow-run receipt and the two
logarithmic span inequalities of the actual Core16 inlet. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Filter Finset Lattice RG Wilson RGComparison.Core16 PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Classical BigOperators Topology
variable {G : Gauge}

def height (R : Run G) (N : ℕ) := Nat.ceil (R.alloy.B.a.clock.hatBeta N)

theorem uniform_dates (R : Run G) (simple : G.Simple) (m s W Q : ℕ) :
    ∀ᶠ k:ℕ in atTop, ∀ N, k≤N →
      4≤height R N ∧ 2*(m:ℝ)≤height R N ∧
        2*layerCost R.alloy.B.a.clock.kernel.penalty s m W Q*4^(halfOrder W Q)≤height R N := by
  let C:=2*layerCost R.alloy.B.a.clock.kernel.penalty s m W Q*4^(halfOrder W Q)
  obtain ⟨i,h⟩:=eventually_atTop.mp ((Next.Rank.Station.hat_rate R.alloy.B.a simple).eventually_ge_atTop
    (max (max 4 (2*(m:ℝ))) C))
  filter_upwards [eventually_ge_atTop i] with k hk
  intro N hN
  have a:= (h N (hk.trans hN)).trans (Nat.le_ceil _)
  have four := ((le_max_left (4:ℝ) (2*m)).trans (le_max_left _ C)).trans a
  exact ⟨by exact_mod_cast four,((le_max_right (4:ℝ) (2*m)).trans (le_max_left _ C)).trans a,
    (le_max_right _ C).trans a⟩

theorem calendar_expenses (R : Run G) (simple : G.Simple) {k N per : ℕ}
    (T : Slices R.family.path.levels per) (hk : k≤N) (W : ℕ)
    (slow : ∀ j, ((R.alloy.B.a.budget j).supportExponent+1)*
      (((R.alloy.B.a.S.block (j-1)).val:ℝ)^4) ≤ Real.sqrt (R.alloy.B.a.clock.hatBeta j))
    (lower : ((N-k:ℕ):ℝ)*Real.log 3≤R.family.S.scale N-R.family.S.scale k)
    (upper : R.family.S.scale N-R.family.S.scale k≤(W:ℝ)*Real.log (R.alloy.B.a.clock.hatBeta N)) :
    let x:=height R N
    R.alloy.B.a.clock.hatBeta N ≤ x ∧ (R.alloy.B.a.budget N).supportExponent+1≤x ∧
      scale (traversal T hk) ≤ x^W ∧ N-k ≤ W*x ∧ (R.alloy.B.a.budget k).B ≤ 2*x^2 := by
  let A:=R.alloy.B.a
  let b:=A.clock.hatBeta N
  intro x
  have hb : 1<b := A.fits.delayed N
  have xb : b≤(x:ℝ) := Nat.le_ceil _
  have xp : 0<(x:ℝ) := (zero_lt_one.trans hb).trans_le xb
  have l3 : 1≤Real.log 3 := (Real.le_log_iff_exp_le (by norm_num)).2 (by linarith only [Real.exp_one_lt_d9])
  have lb : Real.log b≤x := by linarith only [Real.log_le_sub_one_of_pos (zero_lt_one.trans hb),xb]
  have expCap : (A.budget N).supportExponent+1≤x := by
    have side : (1:ℝ)≤((A.S.block (N-1)).val:ℝ) := by exact_mod_cast (A.S.block (N-1)).property
    exact ((le_mul_of_one_le_right (by linarith only [(A.budget N).exponent_pos]) (one_le_pow₀ side)).trans
      (slow N)).trans ((Real.sqrt_le_self_iff.mpr (Or.inr hb.le)).trans xb)
  have scaled : 0<scale (traversal T hk) := by
    by_contra! fail
    have h:=side_scale (traversal T hk)
    rw [Nat.eq_zero_of_le_zero fail,mul_zero] at h
    exact (A.S.side N per).property.not_ge h.symm.le
  have grow : (scale (traversal T hk):ℝ) ≤ (x:ℝ)^W := by
    apply (Real.log_le_log_iff (by exact_mod_cast scaled) (pow_pos xp _)).1
    rw [log_scale,Real.log_pow]
    exact upper.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (zero_lt_one.trans hb) xb) (Nat.cast_nonneg _))
  have dep : ((N-k:ℕ):ℝ) ≤ (W:ℝ)*x := ((le_mul_of_one_le_right (Nat.cast_nonneg _) l3).trans lower).trans
    (upper.trans (mul_le_mul_of_nonneg_left lb (Nat.cast_nonneg _)))
  have lk : Real.log (A.clock.hatBeta k) ≤ x :=
    (Real.log_le_log (zero_lt_one.trans (A.fits.delayed _)) (monotone_hat A simple hk)).trans lb
  have s2:=pow_le_pow_left₀ (Real.log_nonneg (A.fits.delayed _).le) lk 2
  refine ⟨xb,expCap,by exact_mod_cast grow,by exact_mod_cast dep,?_⟩
  apply Nat.ceil_le.mpr
  push_cast
  linarith only [s2,sq_nonneg (x:ℝ)]

theorem actual_fee (R : Run G) (N per W Q p : ℕ) (large : 2≤R.alloy.B.a.clock.hatBeta N)
    (order : 2*halfOrder W Q≤p) :
    (regulatorRun R.family N per N)^p≤(4/(height R N:ℝ))^(halfOrder W Q) := by
  let b:=R.alloy.B.a.clock.hatBeta N
  let B:=R.family.path.β N per N
  let x:=height R N
  have hB : b/2≤B := (R.T.choice.represents N per N le_rfl).band.1
  have b2 : 2≤b := large
  have b0 : 0<b := by linarith only [b2]
  have h1 : 1≤B := by linarith only [hB,b2]
  have B0:=zero_lt_one.trans_le h1
  have ix : (x:ℝ)≤2*b := by have hc:=Nat.ceil_lt_add_one b0.le; change (Nat.ceil b:ℝ)≤2*b;linarith only [hc,b2]
  have x0 : 0<(x:ℝ) := b0.trans_le (Nat.le_ceil _)
  let g:=regulatorRun R.family N per N
  have g0 : 0≤g := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have g1 : g≤1 := by
    exact (inv_le_one₀ (Real.sqrt_pos.mpr B0)).2 (by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt h1)
  have g2 : g^2 ≤ 4/(x:ℝ) := by
    change (Real.sqrt B)⁻¹^2≤_
    rw [inv_pow,Real.sq_sqrt B0.le,inv_eq_one_div,div_le_div_iff₀ B0 x0]
    linarith only [ix,hB]
  exact (pow_le_pow_of_le_one g0 g1 order).trans ((pow_mul g 2 (halfOrder W Q)).le.trans (pow_le_pow_left₀ (sq_nonneg _) g2 _))

end YM.Integration.InletSusceptibility.Packet
