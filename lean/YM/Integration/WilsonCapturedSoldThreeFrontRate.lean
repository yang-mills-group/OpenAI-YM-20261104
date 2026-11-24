import YM.Integration.WilsonCapturedSoldClockIncome
import YM.Integration.WilsonCapturedSoldRadius

/-! Restoring the widths of the same three purchased inputs. The source
profile, school height and front budget are elected before both regulators. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCapturedSoldThreeFrontRate
open Filter Finset Lattice Wilson RG Marker Poly QuadraticLocal PhysicalNext.Repeat.Legato
open QuadraticLocal.Advent Push.PriceCompiler Pert.Asymptotics WilsonCapturedSoldRadius
open scoped Classical BigOperators Topology

def board (M:ℝ)(h:ℕ):ℝ:=(1+M)*(1+10000*(2:ℝ)^(h+15))*4^25
def Ready {G:Gauge}(R:Run G)(M:ℝ)(height j:ℕ):Prop:=
  let H:=R.alloy.B.a.clock.hatBeta j
  64 ≤ H ∧ board M height ≤ H ∧ budgetR R j ≤ 2*H ∧ budgetR R (j+1) ≤ 4*H ∧
    R.alloy.B.a.clock.hatBeta ((j+1)+1) ≤ 4*H

private theorem page {G:Gauge}(R:Run G)(j:ℕ):budgetR R j ≤ R.alloy.B.a.clock.hatBeta (j+1):=by
  have hot:1 ≤ R.alloy.B.a.clock.hatBeta (j+1):=(R.alloy.B.a.fits.delayed _).le
  exact (min_le_right _ _).trans ((Real.rpow_le_rpow_of_exponent_le hot
    (show Beaming.grain (R.alloy.B.a.clock.J j) ≤ 1 by unfold Beaming.grain;apply (div_le_one (by positivity)).2;simp)).trans_eq (Real.rpow_one _))

theorem calendar {G:Gauge}(R:Run G)(simple:G.Simple)(M:ℝ)(h:ℕ):∀ᶠj:ℕ in atTop,Ready R M h j:=by
  obtain ⟨m,drift⟩:=eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)
  have reach:=Next.Rank.Station.hat_rate R.family.path.levels simple
  filter_upwards [eventually_ge_atTop m,reach.eventually_ge_atTop 64,reach.eventually_ge_atTop (board M h)] with j late warm earnings
  have first:=drift j late
  have second:=drift (j+1) (late.trans (Nat.le_succ j))
  have χ:R.alloy.B.a.clock.hatBeta ((j+1)+1) ≤ 4*R.alloy.B.a.clock.hatBeta j:=by linarith
  exact ⟨warm,earnings,(page R j).trans first,(page R (j+1)).trans χ,χ⟩

theorem upper (height:ℕ){χ H M net:ℝ}(M0:0 ≤ M)(warm:64 ≤ H)(f:1 ≤ χ)(dial:χ ≤ 4*H)
    (size:net ≤ M*χ)(date:board M height ≤ H):
    openingInvoice net χ height 15 ≤ H^26:=by
  have a:0 ≤ χ:=zero_le_one.trans f
  have u:1+net ≤ (1+M)*χ:=by linarith
  have h24:χ ≤ χ^24:=by simpa using (pow_le_pow_right₀ f (by omega : 1 ≤ 24))
  have v:χ+10000*2^(height+15)*χ^24 ≤ (1+10000*2^(height+15))*χ^24:=by linarith
  have c₀:0 ≤ 10000*(2:ℝ)^(height+15):=by positivity
  have H₀:0 ≤ H:=by linarith
  unfold openingInvoice
  change (1+net)*(χ+10000*(2:ℝ)^(height+15)*χ^24) ≤ _
  calc
    _ ≤ ((1+M)*χ)*((1+10000*2^(height+15))*χ^24):=mul_le_mul u v (by positivity) (by positivity)
    _=(1+M)*(1+10000*2^(height+15))*χ^25:=by ring
    _ ≤ (1+M)*(1+10000*2^(height+15))*(4*H)^25:=by gcongr
    _=board M height*H^25:=by unfold board;ring
    _ ≤ H*H^25:=mul_le_mul_of_nonneg_right date (pow_nonneg H₀ _)
    _=_:=by ring

theorem retail {H χ b b₁ τ ε p d:ℝ}(hot:64 ≤ H)(x0:0 ≤ χ)(xx:χ ≤ 4*H)
    (b0:0 ≤ b₁)(b₀:b ≤ 2*H)(b₁₀:b₁ ≤ 4*H)(τ₀:τ ≤ 1)(ep:ε ≤ 1)
    (first:p ≤ H^26)(second:d ≤ p*χ*max 1 (max (b*b₁) (τ+ε))):d ≤ H^30:=by
  have H₀:0 ≤ H:=by linarith
  have higher:1 ≤ H:=by linarith
  have sq:1 ≤ H^2:=one_le_pow₀ higher
  have leap:max 1 (max (b*b₁) (τ+ε)) ≤ 8*H^2:=by
    have total:b*b₁ ≤ (2*H)*(4*H):=mul_le_mul b₀ b₁₀ b0 (by positivity)
    apply max_le <;> [linarith;apply max_le <;> nlinarith only [sq,τ₀,ep,total]]
  calc
    d ≤ _:=second
    _ ≤ H^26*(4*H)*(8*H^2):=by gcongr
    _=32*H^29:=by ring
    _ ≤ H*H^29:=mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg H₀ _)
    _=_:=by ring

theorem front {J:Census (Fin 3)} (s:J.Mode){H cash:ℝ}{w:Fin 3→ℝ}
    (hot:64 ≤ H)(bought:cash ≤ H^6)(pw:∀v,0 < w v)(rent:∀v,(w v)⁻¹ ≤ H^30):
    4*cash ≤ Poly.toll w s*H^97:=by
  have h:1 ≤ H:=by linarith
  have h₀:0 ≤ H:=zero_le_one.trans h
  have W:0 < Poly.toll w s:=prod_pos fun i _=>pw i
  have val:s.val.card ≤ 3:=by simpa using Finset.card_le_univ s.val
  have inverse:(Poly.toll w s)⁻¹ ≤ H^90:=by
    unfold Poly.toll;rw [←Finset.prod_inv_distrib]
    calc
      _ ≤ ∏_v∈s.val,H^30:=prod_le_prod (fun i _=>inv_nonneg.mpr (pw i).le) (fun i _=>rent i)
      _=H^(30*s.val.card):=by simp [pow_mul]
      _ ≤ _:=pow_le_pow_right₀ h (by omega)
  have prod:(Poly.toll w s)⁻¹*(4*cash) ≤ H^97:=by
    calc
      _ ≤ (Poly.toll w s)⁻¹*(4*H^6):=by gcongr
      _ ≤ H^90*(4*H^6):=mul_le_mul_of_nonneg_right inverse (by positivity)
      _ ≤ H^90*(H*H^6):=by gcongr;linarith
      _=_:=by ring
  calc
    4*cash=Poly.toll w s*((Poly.toll w s)⁻¹*(4*cash)):=by field_simp [W.ne']
    _ ≤ _:=mul_le_mul_of_nonneg_left prod W.le

theorem strip {σ H:ℝ}(h:64 ≤ H)(width:σ⁻¹ ≤ Real.sqrt (Real.log H)):
    (σ/8)⁻¹ ≤ H:=by
  have h₀:0 < H:=by linarith
  have root:Real.sqrt (Real.log H) ≤ Real.sqrt H:=
    Real.sqrt_le_sqrt ((Real.log_le_sub_one_of_pos h₀).trans (by linarith))
  have sq:=Real.sq_sqrt h₀.le
  have eight:8 ≤ Real.sqrt H:=by nlinarith [Real.sqrt_nonneg H]
  rw [inv_div,div_eq_mul_inv];nlinarith [width.trans root,mul_nonneg (show 0 ≤ Real.sqrt H-8 by linarith) (Real.sqrt_nonneg H)]

end YM.Integration.WilsonCapturedSoldThreeFrontRate
