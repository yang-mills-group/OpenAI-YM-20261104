import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskComplete

/-! Period-independent price of every input in the restored old site, using
the actual cover radius, ordered path salaries and incoming draw. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedRunAction
open Finset Lattice RG Wilson Stationary
open scoped Classical BigOperators

def maskSpringConstant (G : Gauge) (d M : ℕ) : ℝ :=
  2*(Fintype.card PlaqAxes:ℝ)*625+gramCost G 1*4*631+2*(8*8+16*10)+
  9*(M:ℝ)*maskRosterPrice 1 d*(628+2*((d:ℝ)+2))

theorem cap_le_mask_rent (G : Gauge) (c : Clip) (p : BudgetPoint) {u D σ C : ℝ}
    (u0 : 0<u) (D0 : 0≤D) (s0 : 0<σ) (C0 : 0≤C) (d M : ℕ) (γ α β : ℝ) :
    maskSpringCap G c D C d M γ α β≤ maskSpringRent G c p u D σ C d M γ α β := by
  have b1:1≤(((2*p.B+1)^4:ℕ):ℝ):=by exact_mod_cast one_le_pow₀ (by omega:1≤2*p.B+1)
  have pay : 0≤ maskRosterPrice C d:=by unfold maskRosterPrice;positivity
  have gr : 0≤gramCost G D:=by unfold gramCost;positivity
  have face : 0≤faceMaskCap G c:=by unfold faceMaskCap;positivity
  have step : quadraticMaskCap G c D≤quadraticMaskRent G c p u D := by
    unfold quadraticMaskCap quadraticMaskRent
    apply add_le_add (le_mul_of_one_le_right face b1)
    rw [mul_comm 4]
    apply le_mul_of_one_le_right (by positivity)
    linarith [inv_pos.mpr u0]
  unfold maskSpringCap maskSpringRent
  apply add_le_add (add_le_add (mul_le_mul_of_nonneg_left step (abs_nonneg _)) _) _
  · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply add_le_add <;> apply mul_le_mul_of_nonneg_left _ D0
    · exact le_mul_of_one_le_right (by norm_num) (by linarith [inv_pos.mpr u0])
    · exact le_mul_of_one_le_right (by norm_num) (by linarith [inv_pos.mpr u0])
  · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg M)
    exact le_mul_of_one_le_right pay (by linarith [inv_pos.mpr s0,Nat.cast_nonneg (α:=ℝ) d])

theorem mask_spring_growth (G : Gauge) (c : Clip) (p : BudgetPoint) {u D σ C w γ α β : ℝ}
    (one : 1≤w) (q0 : |γ|≤1) (a0 : |α|≤w) (b0 : |β|≤3*w)
    (direct : |c.direct|≤1) (D0 : 0≤D) (paths : D≤w) (u0 : 0<u) (width : u⁻¹≤w)
    (s0 : 0<σ) (aperture : σ⁻¹≤w) (C0 : 0≤C) (bank : C≤3*w)
    (cover : (((2*p.B+1)^4:ℕ):ℝ)≤625*w^8) (d M M₀ : ℕ) (count : M≤M₀) :
    maskSpringRent G c p u D σ C d M γ α β≤ maskSpringConstant G d M₀*w^10 := by
  let b:ℝ:=((2*p.B+1)^4:ℕ)
  let a:ℝ:=Fintype.card PlaqAxes
  let H:=gramCost G 1
  have hn : 0≤H:=by dsimp [H,gramCost];positivity
  have wp : 0≤w:=zero_le_one.trans one
  have f8 : 1≤w^8:=one_le_pow₀ one
  have w8 : w≤w^8:=by simpa only [pow_one] using pow_le_pow_right₀ one (by decide:1≤8)
  have f10 : w^8≤w^10:=pow_le_pow_right₀ one (by decide)
  have w3 : w^3≤w^10:=pow_le_pow_right₀ one (by decide)
  have facePrice : faceMaskCap G c≤2*a:=by
    unfold faceMaskCap;calc _≤a*(1*2):=by dsimp only [a];gcongr
                            _=2*a:=by ring
  have grPrice : gramCost G D≤H*w^2:=by
    have same : gramCost G D=H*D^2:=by dsimp [H,gramCost];ring
    rw [same];gcongr
  have rough : 5+b+u⁻¹≤631*w^8:=by linarith
  have quad : quadraticMaskRent G c p u D≤(2*a*625+H*4*631)*w^10 := by
    change faceMaskCap G c*b+gramCost G D*4*(5+b+u⁻¹)≤_
    have z0 : 0≤b:=by dsimp only [b];positivity
    have faceCap : faceMaskCap G c*b≤(2*a*625)*w^10:=calc
      _≤(2*a)*(625*w^8):=mul_le_mul facePrice cover z0 (by dsimp [a];positivity)
      _=(2*a*625)*w^8:=by ring
      _≤_:=mul_le_mul_of_nonneg_left f10 (by dsimp [a];positivity)
    apply (add_le_add faceCap
      (mul_le_mul (mul_le_mul_of_nonneg_right grPrice (by norm_num : (0:ℝ)≤4)) rough
        (by linarith [inv_pos.mpr u0]) (by positivity))).trans_eq
    ring
  have qu : 0≤quadraticMaskRent G c p u D:=by dsimp [quadraticMaskRent,faceMaskCap,gramCost];positivity
  have left : |γ| *quadraticMaskRent G c p u D≤(2*a*625+H*4*631)*w^10 :=
    (mul_le_of_le_one_left qu q0).trans quad
  have mid : |γ+α|≤2*w:=(abs_add_le γ α).trans (by linarith)
  have h3 : 7+u⁻¹≤8*w:=by linarith
  have h4 : 9+u⁻¹≤10*w:=by linarith
  have middle : |γ+α| *(D*(8*(7+u⁻¹))+D*(16*(9+u⁻¹)))≤(2*(8*8+16*10))*w^10 := by
    calc
      _≤(2*w)*(w*(8*(8*w))+w*(16*(10*w))):=by gcongr
      _=(2*(8*8+16*10))*w^3:=by ring
      _≤_:=mul_le_mul_of_nonneg_left w3 (by norm_num)
  let P:=maskRosterPrice 1 d
  have pp : 0≤P:=by dsimp [P,maskRosterPrice];positivity
  have rp0 : 0≤ maskRosterPrice C d:=by unfold maskRosterPrice;positivity
  have cp : maskRosterPrice C d≤3*P*w := by
    have same : maskRosterPrice C d=P*C:=by dsimp [P,maskRosterPrice];ring
    rw [same];calc _≤P*(3*w):=mul_le_mul_of_nonneg_left bank pp
                   _=3*P*w:=by ring
  let k:=628+2*((d:ℝ)+2)
  have k0 : 0≤k:=by dsimp only [k];positivity
  have shape : 1+2*((d:ℝ)+2)+625+σ⁻¹≤k*w:=by
    have h:0≤(d:ℝ):=Nat.cast_nonneg _
    have q:=mul_le_mul_of_nonneg_left one (show 0≤2*((d:ℝ)+2) by positivity)
    dsimp only [k]
    nlinarith
  have right : |β| *((M:ℝ)*(maskRosterPrice C d*(1+2*((d:ℝ)+2)+625+σ⁻¹)))≤
      (9*(M₀:ℝ)*P*k)*w^10 := by
    have hi : (M:ℝ)≤M₀:=by exact_mod_cast count
    calc
      _≤(3*w)*((M₀:ℝ)*((3*P*w)*(k*w))):=by gcongr
      _=(9*(M₀:ℝ)*P*k)*w^3:=by ring
      _≤_:=mul_le_mul_of_nonneg_left w3 (by positivity)
  apply (add_le_add (add_le_add left middle) right).trans_eq
  dsimp only [maskSpringConstant,a,H,P,k]
  ring

end YM.Integration.OriginalMarkedRunAction
