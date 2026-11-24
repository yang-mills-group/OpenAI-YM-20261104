import YM.Integration.WilsonOriginalPublicPlantedShortGram

/-! The actual independent inversion board buys a fixed-power error on a gross
raw word before any cancellation between the fitted words. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPublicPlantedPeriod
open Filter Set Lattice XSpace
open scoped Classical BigOperators Topology
variable (F:XSpace.Run)
private def speed := Real.log F.ratio
private theorem pos : 0<speed F:=Real.log_pos (show 1<(F.ratio:ℝ) by
  exact_mod_cast (show 1<F.ratio from (by decide:1<3).trans_le F.large))
private theorem last : 0≤Real.log (F.finalSide.side.val:ℝ):=Real.log_nonneg
  (by exact_mod_cast F.finalSide.side.pos)
private theorem scale (j:ℕ) : Real.log (F.step j).spacing= -((j:ℝ)*speed F):=by
  change Real.log (((F.den j:ℕ):ℝ)⁻¹)=_
  simp [XSpace.Run.den,Real.log_pow,speed]
private theorem size (j:ℕ) : Real.log (F.step j).size=Real.log (F.finalSide.side.val:ℝ)+
    ((F.reserve:ℝ)*j*j)*speed F:=by
  rw [Mesh.run_size,Real.log_mul (by exact_mod_cast F.finalSide.side.pos.ne')
    (pow_pos (by exact_mod_cast (show 0<F.ratio from (by decide:0<3).trans_le F.large)) _).ne',
    Real.log_pow]
  push_cast
  rfl
private theorem age (j:ℕ)(hj:1≤j) : -Real.log (F.step j).spacing≤Real.log (F.step j).size:=by
  rw [scale,size,neg_neg]
  have h:(1:ℝ)≤j:=by exact_mod_cast hj
  have p:(1:ℝ)≤F.reserve:=by exact_mod_cast F.spare
  have a:(j:ℝ)≤(F.reserve:ℝ)*j*j:=by
    calc (j:ℝ)=1*1*j:=by ring
         _≤_:=by gcongr
  exact (mul_le_mul_of_nonneg_right a (pos F).le).trans (le_add_of_nonneg_left (last F))
private theorem ages : Tendsto (fun j:ℕ=>Real.log (F.step j).size) atTop atTop:=by
  have clock:Tendsto (fun j:ℕ=>(j:ℝ)*speed F) atTop atTop:=
    by simpa only [mul_comm _ (speed F)] using ((tendsto_const_mul_atTop_of_pos (pos F)).mpr (tendsto_natCast_atTop_atTop (R:=ℝ)))
  apply tendsto_atTop_mono' atTop _ clock
  filter_upwards [eventually_ge_atTop 1] with j hj
  simpa only [scale,neg_neg] using age F j hj

theorem quadratic {b:ℝ}(bpos:0<b)(v:ℕ):∀ᶠ j:ℕ in atTop,
    (F.step j).size^(-b)≤(F.step j).spacing^v:=by
  have slope:= (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop ((v:ℝ)/b)
  filter_upwards [slope] with j late
  have h:(v:ℝ)≤ b*(F.reserve:ℝ)*j:=by
    calc (v:ℝ)≤(j:ℝ)*b:=(div_le_iff₀ bpos).mp late
         _≤b*(F.reserve:ℝ)*j:=by
           have p:(1:ℝ)≤F.reserve:=by exact_mod_cast F.spare
           nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left p bpos.le) (Nat.cast_nonneg j)]
  rw [Real.rpow_def_of_pos (F.step j).size_pos,←Real.exp_log (pow_pos (F.step j).positive v),
    Real.log_pow,scale,size]
  apply Real.exp_le_exp.mpr
  have f:=mul_le_mul_of_nonneg_right h (mul_nonneg (Nat.cast_nonneg j) (pos F).le)
  nlinarith only [f,mul_nonneg bpos.le (last F)]

/-- Gross engineering, raw finite differences and any polynomially distant
spectator are allowed to spend their complete prices on the inversion error. -/
theorem original (C b:ℝ)(cp:0≤C)(hp:0<b)(k h f c p:ℕ):∀ᶠ j:ℕ in atTop,
    ∀T:ℝ,0≤T → T≤((F.step j).spacing⁻¹)^f →
    C*(1+Real.log ((F.step j).size/(F.step j).spacing))^k*
      ((F.step j).spacing⁻¹)^h*(1+T)^c*(F.step j).size^(-b)≤(F.step j).spacing^p := by
  let B:=b/2
  have hb:0<B:=by dsimp [B];positivity
  have trim:Tendsto (fun x:ℝ=>x^k*Real.exp (-(B*x))) atTop (𝓝 0):=by
    simpa [neg_mul] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k:ℝ) B hb
  let C₀:=C*2^c*3^k
  have limit:Tendsto (fun j:ℕ=> C₀*((Real.log (F.step j).size)^k*
      Real.exp (-(B*Real.log (F.step j).size)))) atTop (𝓝 0):=by
    simpa using (trim.comp (ages F)).const_mul C₀
  filter_upwards [limit.eventually_le_const (show (0:ℝ)<1 by norm_num),
    (ages F).eventually_ge_atTop 1,eventually_ge_atTop 1,quadratic F hb (h+f*c+p)] with j cut high one power
  intro T tp cap
  let δ:=(F.step j).spacing
  let P:=(F.step j).size
  have dp:0<δ:=(F.step j).positive
  have pp:0<P:=(F.step j).size_pos
  have ds:δ≤1:=by
    apply (Real.log_le_log_iff dp zero_lt_one).mp
    change Real.log (F.step j).spacing≤_
    rw [scale,Real.log_one]
    exact neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg j) (pos F).le)
  have dinv:1≤δ⁻¹:=(one_le_inv₀ dp).mpr ds
  have low:0≤Real.log (P/δ):=by
    rw [Real.log_div pp.ne' dp.ne'];change 0≤Real.log (F.step j).size-Real.log (F.step j).spacing
    rw [scale];linarith [mul_nonneg (Nat.cast_nonneg j) (pos F).le]
  have structural:1+Real.log (P/δ)≤3*Real.log P:=by
    rw [Real.log_div pp.ne' dp.ne']
    linarith [age F j one]
  have spectator:1+T≤2*(δ⁻¹)^f:=by linarith [show (1:ℝ)≤(δ⁻¹)^f from one_le_pow₀ dinv]
  have wages : C*2^c*(1+Real.log (P/δ))^k*P^(-B)≤1:=by
    calc
      _≤C*2^c*(3*Real.log P)^k*P^(-B):=by gcongr
      _=C₀*((Real.log (F.step j).size)^k*Real.exp (-(B*Real.log (F.step j).size))):=by
        rw [Real.rpow_def_of_pos pp,mul_pow];dsimp only [C₀,P];ring_nf
      _≤_:=cut
  have powSplit: P^(-b)=P^(-B)*P^(-B):=by
    rw [←Real.rpow_add pp];congr 1;dsimp [B];ring
  change C*(1+Real.log (P/δ))^k*(δ⁻¹)^h*(1+T)^c*P^(-b)≤δ^p
  calc
    _≤C*(1+Real.log (P/δ))^k*(δ⁻¹)^h*(2*(δ⁻¹)^f)^c*P^(-b):=by gcongr
    _=(C*2^c*(1+Real.log (P/δ))^k*P^(-B))*((δ⁻¹)^(h+f*c)*P^(-B)):=by
      rw [powSplit,mul_pow,pow_add,pow_mul];ring
    _≤1*((δ⁻¹)^(h+f*c)*δ^(h+f*c+p)):=by gcongr
    _=δ^p:=by rw [one_mul,pow_add δ (h+f*c) p,inv_pow,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ dp.ne'),one_mul]

/-- Every coordinate is clear of both inversion fixed points and every
periodic image, including the stencil's whole support of radius P/16. -/
theorem clear (m:Mesh)(x:Four ℝ)(center:x∈m.Box)(a:Axis)(z:ℝ)
    (offset:|z| ≤ m.size/16)(k:ℤ):m.size/16≤|x a+z-(k:ℝ)*(m.size/2)|:=by
  have half : 0≤ m.size/2 := div_nonneg m.size_pos.le (by norm_num)
  rcases le_or_gt k 0 with h|h
  · have kn:(k:ℝ)≤0:=by exact_mod_cast h
    apply le_trans _ (le_abs_self _)
    linarith [center.1 a,neg_le_of_abs_le offset,mul_nonpos_of_nonpos_of_nonneg kn half]
  · have kn:(1:ℝ)≤k:=by exact_mod_cast (show (1:ℤ)≤k by omega)
    apply le_trans _ (neg_le_abs _)
    linarith [center.2 a,le_of_abs_le offset,mul_le_mul_of_nonneg_right kn half]

end YM.Integration.WilsonOriginalPublicPlantedPeriod
