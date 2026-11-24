import YM.Integration.WilsonRegisteredRectangleFrameCalendar
import YM.Integration.WilsonRegisteredLogFare

/-! Physical range of the original retained-square gate and the true path width on a late date. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonRegisteredRectangleChannelClock
open Filter Lattice RG Wilson OPE.Therm
open scoped Classical Topology
variable {G:Gauge}

def radius (c:Clip)(θ:ℝ):ℕ:=6+⌈max 0 (c.relaxation*Real.log (2/θ))⌉₊

theorem cost (A:Levels G)(m:ℕ):
    let p:=A.params (m+1)
    1+p.paths+p.width⁻¹+p.columns+p.clip.relaxation+p.supportExponent≤((A.S.block m).val:ℝ):=by
  let p:=A.params (m+1)
  let L:ℝ:=(A.S.block m).val
  have large:1<L:=by
    unfold L
    exact_mod_cast (show 1<(A.S.block m).val from lt_of_lt_of_le (by decide) (A.S.block_large m))
  let K:ℝ:=A.clock.J (m+1)
  have order:1≤K:=by
    have hz:=A.clock.adm (m+1)
    unfold K;exact_mod_cast (by omega : 1≤A.clock.J (m+1))
  let x:=1+p.paths+p.width⁻¹+p.columns+p.clip.relaxation+p.supportExponent
  have xp:0<x:=by
    dsimp only [x]
    linarith only [p.paths_pos,p.columns_ge,p.price_pos,p.clip.radius_pos,inv_nonneg.mpr p.width_pos.le]
  have cap:(K^2)⁻¹≤1:=(inv_le_one₀ (by positivity)).mpr (by nlinarith only [order,sq_nonneg (K-1)])
  have sale:Real.log x/Real.log L≤(K^2)⁻¹:=A.fits.logCost m
  exact (Real.log_le_log_iff xp (zero_lt_one.trans large)).mp ((div_le_one (Real.log_pos large)).mp (sale.trans cap))

theorem threshold {b θ:ℝ}(bp:2≤b)(hint:(Real.sqrt b)⁻¹≤θ):Real.log (2/θ)≤2*Real.log b:=by
  have b0:0<b:=by linarith
  have s0:0<Real.sqrt b:=Real.sqrt_pos.mpr b0
  have t0:0<θ:=(inv_pos.mpr s0).trans_le hint
  have inv:θ⁻¹≤Real.sqrt b:=by
    simpa only [inv_inv] using (inv_le_inv₀ t0 (inv_pos.mpr s0)).mpr hint
  have db:Real.sqrt b≤b:=(Real.sqrt_le_iff).mpr ⟨b0.le,by nlinarith only [mul_nonneg b0.le (show 0≤b-1 by linarith)]⟩
  have sale:2/θ≤b^2:=by rw [div_eq_mul_inv];nlinarith only [inv.trans db,mul_nonneg b0.le (show 0≤b-2 by linarith)]
  exact (Real.log_le_log (by positivity) sale).trans_eq (by rw [Real.log_pow];norm_num)

theorem range {b θ:ℝ}(c:Clip)(B:ℕ)(large:4≤Real.log b)(bp:2≤b)(hint:(Real.sqrt b)⁻¹≤θ)
    (size:c.relaxation≤2*Real.log b)(floor:(Real.log b)^2≤(B:ℝ)):1+radius c θ≤B^2:=by
  let t:=Real.log b
  have ln:=threshold bp hint
  have t0:0≤t:=by linarith only [large]
  have toll:c.relaxation*Real.log (2/θ)≤(2*t)*(2*t):=
    (mul_le_mul_of_nonneg_left ln c.radius_pos.le).trans (mul_le_mul_of_nonneg_right size (by positivity))
  have ran:max 0 (c.relaxation*Real.log (2/θ))≤(2*t)*(2*t):=max_le (mul_nonneg (by positivity) (by positivity)) toll
  have cap:((1+radius c θ:ℕ):ℝ)≤4*t^2+8:=by
    simp only [radius,Nat.cast_add,Nat.cast_one]
    have ceil:=Nat.ceil_lt_add_one (le_max_left (0:ℝ) (c.relaxation*Real.log (2/θ)))
    norm_num
    linarith only [ceil,ran]
  have x:4*t^2+8≤(t^2)^2:=by
    have lo:8≤t^2:=by nlinarith only [large,sq_nonneg (t-4)]
    nlinarith only [sq_nonneg (t^2-8),lo]
  exact_mod_cast cap.trans (x.trans (pow_le_pow_left₀ (sq_nonneg t) floor 2))

end YM.Integration.WilsonRegisteredRectangleChannelClock
