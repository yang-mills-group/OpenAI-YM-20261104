import YM.Integration.WilsonPositionOriginalDressedQPaidAppointment
import YM.Integration.WilsonRootedKioskPostRadius

/-! Restore every original marker wallet and pay the three spatial cuts on
the native square-log path radius, before the period or sources are read. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQCutClock
open Function Filter Finset Lattice RG Marker QuadraticLocal Pressure
open WilsonPositionOriginalDressedQCutSquare
open scoped Classical Topology BigOperators

private theorem flat (E q:ℕ)(C:ℝ):∀ᶠ y:ℝ in atTop,
    C*y^E/Real.exp (radiusB y)  ≤  (y^q)⁻¹:=by
  filter_upwards [eventually_ge_atTop 1,eventually_ge_atTop C,
    Real.tendsto_log_atTop.eventually_ge_atTop (E+1+q:ℕ)] with y hy hC hlog
  have yp:0<y:=zero_lt_one.trans_le hy
  have hl:0 ≤ Real.log y:=Real.log_nonneg hy
  have sq:((E+1+q:ℕ):ℝ)*Real.log y  ≤  (radiusB y:ℝ):=
    (mul_le_mul_of_nonneg_right hlog hl).trans (by simpa only [←sq,radiusB] using Nat.le_ceil ((Real.log y)^2))
  have power:y^(E+1+q)  ≤  Real.exp (radiusB y):=by
    simpa only [Real.exp_nat_mul,Real.exp_log yp] using Real.exp_le_exp.mpr sq
  rw [←one_div,div_le_div_iff₀ (Real.exp_pos _) (pow_pos yp q),one_mul]
  calc
    _  ≤  (y *y^E)*y^q:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (pow_nonneg yp.le _)) (pow_nonneg yp.le _)
    _ = y^(E+1+q):=by rw [pow_add,pow_succ];ring
    _  ≤  _:=power

variable {V:Type} [DecidableEq V] [Fintype V] (w:V→ℝ)
local notation "Γ" => Stock.census V

private theorem restore (positive:∀v,0<w v){y Ω C d:ℝ}{b cap:ℕ}
    (hy:1  ≤  y)(cost:1  ≤  C)(oo:1  ≤  Ω)(oy:Ω  ≤  y)
    {v:V→ℝ}(hw:∀j,0<v j)(canc:∀s:(Γ).Mode,Poly.toll v s*(C*y^(b+1)*Ω)^s.val.card=Poly.toll w s)
    (pos:0  ≤  d)(wage:d  ≤  y^cap*Ω)(s:(Γ).Mode):
    bound (w:=v) (d:=d) s  ≤ 
      ((1+∑t:(Γ).Mode,(Poly.toll w t)⁻¹)*C^(Fintype.card V))*
        y^(cap+1+(b+2)*Fintype.card V):=by
  let h:=Fintype.card V
  let W:ℝ:=1+∑t:(Γ).Mode,(Poly.toll w t)⁻¹
  have Wp:0  ≤  W:= add_nonneg zero_le_one (sum_nonneg fun j _=> (inv_pos.mpr (Poly.worth positive j)).le)
  have charge:(Poly.toll w s)⁻¹  ≤  W:=by
    have t: (Poly.toll w s)⁻¹  ≤  ∑t:(Γ).Mode,(Poly.toll w t)⁻¹:=
      single_le_sum (fun j _=> (inv_pos.mpr (Poly.worth positive j)).le) (mem_univ s)
    exact t.trans (le_add_of_nonneg_left zero_le_one)
  have count:s.val.card  ≤  h:=card_le_univ s.val
  have yp:0  ≤  y:=zero_le_one.trans hy
  have cp:0  ≤  C:=zero_le_one.trans cost
  have zpos:0<C*y^(b+1)*Ω:=mul_pos (mul_pos (zero_lt_one.trans_le cost)
    (pow_pos (zero_lt_one.trans_le hy) _)) (zero_lt_one.trans_le oo)
  have iden:(Poly.toll v s)⁻¹=(Poly.toll w s)⁻¹*(C*y^(b+1)*Ω)^s.val.card:=by
    rw [←canc s,mul_inv_rev];field_simp [(ne_of_gt zpos), (Poly.worth hw s).ne']
  have atMost:C*y^(b+1)*Ω  ≤  C*y^(b+2):=by
    simpa [pow_succ,mul_assoc] using mul_le_mul_of_nonneg_left oy (mul_nonneg cp (pow_nonneg yp (b+1)))
  have powBound:(C*y^(b+1)*Ω)^s.val.card  ≤  C^h*y^((b+2)*h):=by
    calc _  ≤  (C*y^(b+2))^s.val.card:=pow_le_pow_left₀ zpos.le atMost _
         _  ≤  (C*y^(b+2))^h:=pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le cost (one_le_pow₀ hy)) count
         _ = _:=by rw [mul_pow,pow_mul]
  have stocked:(Poly.toll w s)⁻¹ * (C*y^(b+1)*Ω)^s.val.card  ≤  W*(C^h*y^((b+2)*h)):=
    mul_le_mul charge powBound (pow_nonneg zpos.le _) Wp
  have dw:d  ≤  y^(cap+1):=wage.trans (by simpa [pow_succ] using mul_le_mul_of_nonneg_left oy (pow_nonneg yp cap))
  change (Poly.toll v s)⁻¹*d  ≤  W*C^h*y^(cap+1+(b+2)*h)
  rw [iden]
  calc _  ≤  (W*(C^h*y^((b+2)*h)))*y^(cap+1):=mul_le_mul stocked dw pos (by positivity)
       _ = _:=by rw [pow_add];ring

private lemma combine (y M F Z c a b j:ℝ)(yp:1  ≤  y)(Mp:0  ≤  M)
    (Fp:0  ≤  F)(bp:0  ≤  b)(cp:0  ≤  c)(cz:c  ≤  M*y)
    (la:a  ≤  F*y)(lb:b  ≤  F*y)(lj:j  ≤  F*y)(z:0<Z):
    a/Z*(c+b)+(c+a)*(b/Z)+j/Z  ≤  (2*F*(M+F)+F)*y^2/Z:=by
  have yp':0 ≤ y:=zero_le_one.trans yp
  have one: a*(c+b) ≤ F*y*((M+F)*y):=by
    rw [add_mul M F y];exact mul_le_mul la (add_le_add cz lb) (add_nonneg cp bp) (mul_nonneg Fp yp')
  have two: (c+a)*b ≤ (M+F)*y*(F*y):=by
    rw [add_mul M F y];exact mul_le_mul (add_le_add cz la) lb bp (add_nonneg (mul_nonneg Mp yp') (mul_nonneg Fp yp'))
  have three:j ≤ F*y^2:=lj.trans (mul_le_mul_of_nonneg_left (by nlinarith only [mul_nonneg yp' (sub_nonneg.mpr yp)]:y ≤ y^2) Fp)
  have numerator:a*(c+b)+(c+a)*b+j  ≤  (2*F*(M+F)+F)*y^2:=by
    calc _  ≤  F*y*((M+F)*y)+(M+F)*y*(F*y)+F*y^2:=add_le_add (add_le_add one two) three
         _ = _:=by ring
  calc _ = (a*(c+b)+(c+a)*b+j)/Z:=by ring
       _  ≤  _:=div_le_div_of_nonneg_right numerator z.le

theorem event (positive:∀j,0<w j)(C:ℝ)(cost:1 ≤ C)(M:ℝ)(mp:0 ≤ M)(b cap order q:ℕ):
    ∀ᶠ y:ℝ in atTop,∀x Ω A d:ℝ,1 ≤ x → x ≤ y → 1 ≤ Ω → Ω ≤ y → 1 ≤ A → 0 ≤ d → d ≤ y^cap*Ω →
    ∀(v:V→ℝ), (∀j,0<v j) → (∀s:(Γ).Mode,Poly.toll v s*(C*y^(b+1)*Ω)^s.val.card=Poly.toll w s) →
    ∀a b₀ j:(Γ).Mode,let m:=radiusB y
    tailFee (w:=v) (a:=A) (d:=d) m a*(M*x^order+bound (w:=v) (d:=d) b₀)+
    (M*x^order+bound (w:=v) (d:=d) a)*tailFee (w:=v) (a:=A) (d:=d) m b₀+
    tailFee (w:=v) (a:=A) (d:=d) m j  ≤  (y^q)⁻¹:=by
  let F:ℝ:=(1+∑s:(Γ).Mode,(Poly.toll w s)⁻¹)*C^Fintype.card V
  let E:=cap+1+(b+2)*Fintype.card V
  let h:=max E order
  have wp:0 ≤ 1+∑s:(Γ).Mode,(Poly.toll w s)⁻¹:=add_nonneg zero_le_one
    (sum_nonneg fun j _=> (inv_pos.mpr (Poly.worth positive j)).le)
  have Fp:0 ≤ F:=mul_nonneg wp (pow_nonneg (zero_le_one.trans cost) _)
  have budget:=flat (h*2) q (2*F*(M+F)+F)
  filter_upwards [budget,eventually_ge_atTop (1:ℝ)] with y paid hy
  intro x Ω A d hx xy omega oy ha dp dy v hw canc a b₀ j m
  have raised:∀s:(Γ).Mode,bound (w:=v) (d:=d) s  ≤  F*y^h:=fun s=>
    (restore w positive hy cost omega oy hw canc dp dy s).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy (le_max_left E order)) Fp)
  have small:M*x^order  ≤  M*y^h:=mul_le_mul_of_nonneg_left
    ((pow_le_pow_left₀ (zero_le_one.trans hx) xy order).trans (pow_le_pow_right₀ hy (le_max_right E order))) mp
  have pos(s:(Γ).Mode):0 ≤ bound (w:=v) (d:=d) s:=mul_nonneg (inv_pos.mpr (Poly.worth hw s)).le dp
  have peel(s:(Γ).Mode):tailFee (w:=v) (a:=A) (d:=d) m s=
      bound (w:=v) (d:=d) s/Real.exp (A*m):=by
    simp only [tailFee,bound,mul_inv_rev,div_eq_mul_inv];ring
  rw [peel,peel,peel]
  have estimate:=combine (y^h) M F (Real.exp (A*m)) (M*x^order)
    (bound (w:=v) (d:=d) a) (bound (w:=v) (d:=d) b₀) (bound (w:=v) (d:=d) j)
    (one_le_pow₀ hy) mp Fp (pos _)
    (mul_nonneg mp (pow_nonneg (zero_le_one.trans hx) _)) small (raised _) (raised _) (raised _) (Real.exp_pos _)
  have mg:(m:ℝ) ≤ A*(m:ℝ):=by
    simpa only [one_mul] using (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg m:0 ≤ (m:ℝ)))
  have grow:=Real.exp_le_exp.mpr mg
  rw [←pow_mul] at estimate
  exact estimate.trans ((div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) grow).trans paid)

end YM.Integration.WilsonPositionOriginalDressedQCutClock
