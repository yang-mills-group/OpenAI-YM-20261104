import YM.Integration.WilsonLocalConditionalResidue
import YM.Integration.WilsonRegisteredChartTaylorRate

/-! The measured coupling pays a polynomial in the original logarithmic
angular radius and in the number of changed wires at its full order. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalTerminalChartRate
open Filter Lattice RG Wilson RG16 Pert.Asymptotics PhysicalNext.Repeat.Legato
open WilsonLocalConditionalResidue WilsonPhysicalLocalPlaquetteReserve
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}

theorem inverse {a b:ℝ} (ha:0 < a) (hb:0 < b) (scale:a ≤ 4*b) : (Real.sqrt b)⁻¹ ≤ 2*(Real.sqrt a)⁻¹ := by
  have h:=Real.sqrt_le_sqrt scale
  rw [Real.sqrt_mul (by norm_num:0 ≤ (4:ℝ)),show Real.sqrt 4=2 by norm_num] at h
  simpa only [one_div,div_eq_mul_inv,one_mul] using (show 1/Real.sqrt b ≤ 2/Real.sqrt a from
    (div_le_div_iff₀ (Real.sqrt_pos.mpr hb) (Real.sqrt_pos.mpr ha)).mpr (by simpa only [one_mul] using h))

theorem counted_directions {ι:Type} [Fintype ι] (p l k:ℕ) {H W g Z s A:ℝ} (hH:0 ≤ H) (hW:0 ≤ W) (hg:0 ≤ g)
    (hZ:0 ≤ Z) (hs:1 ≤ s) (hA:1 ≤ A) (card:(Fintype.card ι:ℝ) ≤ Z*s^l)
    (X Y:ι→G.Color) (size:∀i,‖X i‖ ≤ A*s^k ∧ ‖Y i‖ ≤ A*s^k) :
    expense p H W g X Y ≤ (Z*(2*H+12*W)*A^(p+3))*s^(l+k*(p+3))*g*g^p := by
  have hs0:0 ≤ s:=zero_le_one.trans hs
  let B:=A*s^k
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hs)
  have big:B^(p+1) ≤ B^(p+3):=pow_le_pow_right₀ hB (by omega)
  have angular : 2*H*B^(p+1)+12*W*B^(p+3) ≤ (2*H+12*W)*B^(p+3) := by
    rw [add_mul];exact add_le_add (mul_le_mul_of_nonneg_left big (by positivity)) le_rfl
  have bp:0 ≤ B:=zero_le_one.trans hB
  calc
    _ ≤ (Fintype.card ι:ℝ)*g^(p+1)*(2*H*B^(p+1)+12*W*B^(p+3)) := counted p hH hW hg X Y B size
    _ ≤ Z*s^l*g^(p+1)*((2*H+12*W)*B^(p+3)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right card (pow_nonneg hg _)) angular (by positivity) (by positivity)
    _=_ := by dsimp [B];rw [mul_pow,←pow_mul,pow_add s l (k*(p+3)),pow_succ g p];ring

theorem paid (R:Run G) (simple:G.Simple) (p l k:ℕ) (H W Z K:ℝ)
    (hH:0 ≤ H) (hW:0 ≤ W) (hZ:0 ≤ Z) (hK:0 ≤ K) {δ ε:ℝ} (hd:0 < δ) (he:0 < ε) :
    ∀ᶠ m:ℕ in atTop,∀N per,m+1 ≤ N→∀(ι:Type) [Fintype ι] (X Y:ι→G.Color),
    let b:=R.family.path.levels.clock.hatBeta (m+1)
    let g:=regulatorRun R.family N per (m+1)
    (Fintype.card ι:ℝ) ≤ Z*(Real.log b)^l→
    (∀i,g*‖X i‖ ≤ K*(Real.log b)^k*(Real.sqrt b)⁻¹ ∧ g*‖Y i‖ ≤ K*(Real.log b)^k*(Real.sqrt b)⁻¹)→
    (∀i,g*‖X i‖ ≤ δ ∧ g*‖Y i‖ ≤ δ) ∧ expense p H W g X Y ≤ ε*g^p := by
  let A:=max 1 (2*K)
  let M:=Z*(2*H+12*W)*A^(p+3)
  have hA:1 ≤ A:=le_max_left .. 
  have a0:0 ≤ A:=zero_le_one.trans hA
  have m0:0 ≤ M:=by dsimp [M];positivity
  have rise:=(Next.Rank.Station.hat_rate R.family.path.levels simple).comp (tendsto_add_atTop_nat 1)
  filter_upwards [(Real.tendsto_log_atTop.comp rise).eventually_ge_atTop (1:ℝ),rise.eventually (small K k hd),
    rise.eventually (small (2*M) (l+k*(p+3)) he)] with m log_room radius paid N per active ι _ X Y
  let b:=R.family.path.levels.clock.hatBeta (m+1)
  let β:=R.family.path.β N per (m+1)
  let s:=Real.log b
  let g:=regulatorRun R.family N per (m+1)
  let u:=(Real.sqrt b)⁻¹
  change 1 ≤ s at log_room
  have b0:0 < b:=zero_lt_one.trans (R.family.path.levels.fits.delayed _)
  have β0:0 < β:=Overlay.beta_positive R.makes.wilson active
  have g0:0 < g:=inv_pos.mpr (Real.sqrt_pos.mpr β0)
  have s0:0 ≤ s:=zero_le_one.trans log_room
  have band:=(R.makes.wilson.represents N per (m+1) active).band
  have left:b/2 ≤ β:=band.1
  have right:β ≤ 2*b:=band.2
  have ub:b ≤ 4*β:=by linarith only [left,β0]
  have bu:β ≤ 4*b:=by linarith only [right,b0]
  have price:u ≤ 2*g:=inverse β0 b0 bu
  have ceiling:g ≤ 2*u:=inverse b0 β0 ub
  change K*s^k*u ≤ δ at radius
  change 2*M*s^(l+k*(p+3))*u ≤ ε at paid
  dsimp only;intro card size
  have one (x:ℝ) (h:g*x ≤ K*s^k*u) : x ≤ A*s^k := by
    apply le_of_mul_le_mul_left _ g0
    calc
      _ ≤ K*s^k*u:=h
      _ ≤ K*s^k*(2*g):=mul_le_mul_of_nonneg_left price (by positivity)
      _=g*((2*K)*s^k):=by ring
      _ ≤ _:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_right 1 (2*K)) (pow_nonneg s0 _)) g0.le
  refine ⟨fun i=>⟨(size i).1.trans radius,(size i).2.trans radius⟩,?_⟩
  have cash:M*s^(l+k*(p+3))*g ≤ ε:=calc
    _ ≤ M*s^(l+k*(p+3))*(2*u):=mul_le_mul_of_nonneg_left ceiling (by positivity)
    _=2*M*s^(l+k*(p+3))*u:=by ring
    _ ≤ _:=paid
  exact (counted_directions p l k hH hW g0.le hZ log_room hA card X Y (fun i=>⟨one _ (size i).1,one _ (size i).2⟩)).trans
    (mul_le_mul_of_nonneg_right cash (pow_nonneg g0.le p))

end YM.Integration.WilsonLocalTerminalChartRate
