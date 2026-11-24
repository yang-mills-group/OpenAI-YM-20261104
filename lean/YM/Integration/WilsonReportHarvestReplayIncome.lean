import YM.Integration.WilsonReportHarvestReplayPhysical
import YM.Integration.WilsonAllDateHarvestIntervalPrice
import YM.Integration.WilsonMixedTaggedMeasuredWindow

/-! The inverse radii of every three-colour historical mode, after the
complete originally returned three cutoff columns are re-enrolled. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReportHarvestReplayIncome
open Filter Lattice Wilson RG Marker PhysicalNext.Repeat.Legato RG05Readout.Many
open WilsonMeasuredAdmission
open scoped Classical Topology
variable {G:Gauge}

def engineering (d:ℕ):ℕ:=(2*(d+2)+1+(d+1))*3
def reserve (K d H k:ℕ):ℕ:=(3*k+4+k+H+2*(d+2)+2*(K+3)*(d+1))*3

private theorem triple {x a Q σ:ℝ}(xp:1 ≤ x)(ap:1 ≤ a)(qp:0 ≤ Q)(σp:0 ≤ σ)
    (K d H k n:ℕ)(q:Q ≤ x^H*(a^(2*(d+2))*x^(2*(d+2))))
    (room:σ ≤ x^(2*(K+3))*a):
    (x^((3*k+4)*n+k)*(Q*a)*σ^(d+1))^3 ≤
      a^(engineering d)*x^(reserve K d H k*(n+1)):=by
  let u:=2*(d+2)
  let v:=2*(K+3)
  let w:=3*k+4
  let e:=w*n+k+H+u+v*(d+1)
  have x₀:0 ≤ x:=zero_le_one.trans xp
  have a₀:0 ≤ a:=zero_le_one.trans ap
  have one:x^(w*n+k)*(Q*a)*σ^(d+1) ≤ a^(u+1+(d+1))*x^e:=by
    calc _ ≤ x^(w*n+k)*(x^H*(a^u*x^u)*a)*(x^v*a)^(d+1):=
          mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right q a₀) (pow_nonneg x₀ _))
            (pow_le_pow_left₀ σp room _) (pow_nonneg σp _) (by positivity)
         _ = _:=by dsimp only [e];simp only [mul_pow,pow_add,pow_mul,pow_one];ring
  have cmp:e ≤ (w+k+H+u+v*(d+1))*(n+1):=by
    calc e = w*n+(k+H+u+v*(d+1)):=by dsimp [e];omega
         _ ≤ w*(n+1)+(k+H+u+v*(d+1))*(n+1):=Nat.add_le_add
              (Nat.mul_le_mul_left _ (by omega))
              (Nat.le_mul_of_pos_right _ (Nat.succ_pos n))
         _ = _:=by ring
  have scale:e*3 ≤ reserve K d H k*(n+1):=by
    calc _ ≤ ((w+k+H+u+v*(d+1))*(n+1))*3:=Nat.mul_le_mul_right _ cmp
         _ = _:=by unfold reserve;dsimp only [w,u,v];ring
  calc _ ≤ (a^(u+1+(d+1))*x^e)^3:=pow_le_pow_left₀ (by positivity) one 3
       _ = a^(engineering d)*x^(e*3):=by unfold engineering;rw [mul_pow,←pow_mul,←pow_mul]
       _ ≤ _:=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ xp scale) (pow_nonneg a₀ _)

theorem original (R:Run G)(simple:G.Simple)(K:ℕ)(hk:0<K)(d H k p:ℕ)
    {ε:ℝ}(ep:0<ε)(slow:WilsonWindowReportingPace.Slow R.kit):
    ∀ᶠr in 𝓝[>] (0:ℝ),let C:=R.family
      let m:=WilsonMeasuredWindow.stop C.path.levels simple K r
      let b₀:=RG05Readout.crossLevel C.S r-1-1
      ∀b:ℕ,b₀ ≤ b → b ≤ b₀+1 → ∀u≥m,∀i≥m,i ≤ u → WilsonReportHarvestUpperRange.eligible C.S m i u →
      ∀per:ℕ,let N:=u+1
        let Q:=WilsonReportHarvestReplayPhysical.allowance R m N d H
        let Q':=Q*(C.S.a m/C.S.a i)
        let δ:=WilsonReportHarvestReplayPhysical.amount R b m i N per p (engineering d) (reserve K d H k) (ε/2)
        1 ≤ Q' ∧ 2*δ*(WilsonAllDateHarvestIntervalPrice.bill C b i (d+1) k Q')^3 ≤
          ε*((Real.sqrt (C.path.rep N per i).beta)⁻¹)^p := by
  let C:=R.family
  let A:=C.path.levels
  let β:=A.clock.hatBeta
  have growing:=WilsonMeasuredWindow.stop_tendsto A simple K hk
  have dates:=(WilsonMixedTaggedMeasuredWindow.original R simple K hk slow.2).2
  have hot:=(Next.Rank.Station.hat_rate A simple).comp growing
  filter_upwards [dates,hot.eventually_ge_atTop 2,growing.eventually
      (WilsonReportHarvestUpperRange.original R simple d H)]
    with r old warm upper C' m b₀ b lower _ u mu i mi iu eligible per N Q Q' δ
  let a:=C.S.a m/C.S.a i
  let x:=β i
  have ap:1 ≤ a:=(one_le_div (C.S.a_pos _)).2 (C.S.strictAnti.antitone mi)
  have order:β m ≤ x:=beta_le' (C:=C) simple mi
  have xp:1 ≤ x:=(A.fits.delayed i).le
  have hN:=upper u mu i mi iu eligible
  have mpos:1 ≤ (β m)^H:=one_le_pow₀ (A.fits.delayed m).le
  have paid:1 ≤ Q:=one_le_mul_of_one_le_of_one_le mpos hN.1
  have qbound:Q ≤ x^H*(a^(2*(d+2))*x^(2*(d+2))):=
    mul_le_mul (pow_le_pow_left₀ (zero_lt_one.trans (A.fits.delayed m)).le order H)
      hN.2.1 (zero_le_one.trans hN.1) (pow_nonneg (zero_le_one.trans xp) _)
  have positive:0 < β m:=zero_lt_one.trans (A.fits.delayed m)
  have mast:RG05Readout.Lambda A m ≤ x^2:=by
    have priced:RG05Readout.Lambda A m ≤ (β m)^2:=by
      have log:=Real.log_le_sub_one_of_pos positive
      change 2+Real.log (β m) ≤ (β m)^2
      have hm:2 ≤ β m:=warm
      nlinarith only [log,hm,sq_nonneg (β m-1)]
    exact priced.trans (pow_le_pow_left₀ positive.le order 2)
  have span:C.S.a b/C.S.a m ≤ x^(2*(K+3)):=by
    calc _ ≤ C.S.a b₀/C.S.a m:=div_le_div_of_nonneg_right (C.S.strictAnti.antitone lower) (C.S.a_pos m).le
         _ ≤ (RG05Readout.Lambda A m)^(K+3):=old.2.1
         _ ≤ (x^2)^(K+3):=pow_le_pow_left₀ (mast_pos A m).le mast _
         _ = _:=by rw [pow_mul]
  have room:C.S.a b/C.S.a i ≤ x^(2*(K+3))*a:=by
    calc _ = (C.S.a b/C.S.a m)*a:=by dsimp only [a];field_simp [(C.S.a_pos m).ne']
         _ ≤ _:=mul_le_mul_of_nonneg_right span (zero_le_one.trans ap)
  have tally:=triple xp ap (zero_le_one.trans paid) (div_nonneg (C.S.a_pos b).le (C.S.a_pos i).le)
    K d H k (i-b) qbound room
  let g:=(Real.sqrt (C.path.rep N per i).beta)⁻¹
  let α:=a^(engineering d)
  let z:=x^(reserve K d H k*(i-b+1))
  have αp:0<α:=pow_pos (zero_lt_one.trans_le ap) _
  have zp:0<z:=pow_pos (zero_lt_one.trans_le xp) _
  have gp:0 ≤ g:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have bill:(WilsonAllDateHarvestIntervalPrice.bill C b i (d+1) k Q')^3 ≤ α*z:=tally
  have δp:0 ≤ δ:=div_nonneg (div_nonneg (mul_nonneg (half_pos ep).le (pow_nonneg gp _)) αp.le) zp.le
  refine ⟨one_le_mul_of_one_le_of_one_le paid ap,?_⟩
  calc 2*δ*(WilsonAllDateHarvestIntervalPrice.bill C b i (d+1) k Q')^3 ≤ 2*δ*(α*z):=
         mul_le_mul_of_nonneg_left bill (by positivity)
       _ = ε*g^p:=by change 2*((ε/2*g^p)/α/z)*(α*z)=ε*g^p;field_simp [αp.ne',zp.ne']

end YM.Integration.WilsonReportHarvestReplayIncome
