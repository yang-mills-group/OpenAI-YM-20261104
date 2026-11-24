import YM.Contact.Packets
import YM.Contact.SingleBand

/-! Dyadic comparison uniformly in the location of the shrinking test scale. -/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts
open Set Metric Filter Function MeasureTheory
open scoped Topology

def radius (i:ℤ):ℝ:=(2:ℝ)^i
lemma radius_pos (i:ℤ): 0<radius i:= zpow_pos (by norm_num) i
lemma radius_add (i j:ℤ):radius (i+j)=radius i*radius j:=zpow_add₀ (by norm_num) ..

private lemma shift_exists (r:ℝ)(hr:0<r): ∃ n:ℤ, radius n ≤ r ∧ r ≤ 2*radius n:=by
  have h:0 < Real.log 2:= Real.log_pos one_lt_two
  let n:=⌊Real.log r / Real.log 2⌋
  have hr':r ≤ radius (n+1):=by
    rw [radius, Real.le_zpow_iff_log_le hr zero_lt_two, Int.cast_add, Int.cast_one]
    exact le_of_lt ((div_lt_iff₀ h).1 (Int.lt_floor_add_one _))
  refine ⟨n,(Real.zpow_le_iff_le_log zero_lt_two hr).2 ((le_div_iff₀ h).1 (Int.floor_le _)),?_⟩
  rwa [radius_add,show radius 1=2 from zpow_one _,mul_comm (radius _) _] at hr'
private def weights (a b:ℝ) (i:ℤ):ℝ:= if i ≤ 0 then ((2:ℝ)^a)^i else ((2:ℝ)^(-b))^i
private lemma weight_pos(a b : ℝ)(i:ℤ):0<weights a b i:=by dsimp [weights]; split_ifs <;> exact zpow_pos (Real.rpow_pos_of_pos zero_lt_two _) _
private lemma weights_sum{a b:ℝ}(ha:0<a)(hb:0<b): Summable (weights a b):=summable_int_iff_summable_nat_and_neg.mpr (by
  refine ⟨?_,?_⟩
  · have he (i:ℕ):weights a b (i:ℤ)=((2:ℝ)^(-b))^i:=by cases i with
                                                           | zero=>rw [Nat.cast_zero,weights,if_pos le_rfl,zpow_zero,pow_zero]
                                                           | succ i=> dsimp [weights];split_ifs; (exfalso; omega); rw[← Nat.cast_one,← Nat.cast_add,zpow_natCast]
    simpa only [he] using (summable_geometric_of_lt_one (Real.rpow_nonneg zero_le_two _) (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.mpr hb)))
  · have he(i:ℕ):weights a b (-(i:ℤ))= ((2:ℝ)^(-a))^i:=by
       rw [weights,if_pos (show -(i:ℤ)≤0 by omega),zpow_neg,zpow_natCast,← inv_pow,Real.rpow_neg zero_le_two]
    simpa only [he] using (summable_geometric_of_lt_one (Real.rpow_nonneg zero_le_two _) (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.mpr ha))))

/-- Annular envelope gives absolute summability and a uniform bound (not losing log-r) for
any target Banach data. -/
lemma dyadic_payment {E:Type*}[SeminormedAddCommGroup E] {a b:ℝ}(ha:0<a)(hb:0<b):
    ∃ M:ℝ,0≤M∧∀ {r:ℝ}, 0<r→ ∀ (c:ℝ)(z:ℤ→E),0≤c→ (∀ j, ‖z j‖≤ if radius j/r ≤ 1/4 then c*(radius j/r)^a else c*(radius j/r)^(-b)) → Summable (fun j=>‖z j‖) ∧ ‖∑' j,z j‖≤c*M:=by
   let w:=weights a b; let A:=(1/4:ℝ)^a
   let d:=(1/4:ℝ)^(-b)*(1/4:ℝ)^(-a)
   have hp':0 < (1/4:ℝ):=by norm_num
   have hd:1≤d:=one_le_mul_of_one_le_of_one_le (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hp' (by norm_num) (by linarith)) (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hp' (by norm_num) (by linarith))
   have hda:(1/4:ℝ)^(-b) ≤ d:=le_mul_of_one_le_right (Real.rpow_pos_of_pos hp' _).le (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hp' (by norm_num) (by linarith))
   have hA:(1/4:ℝ)^(-b)=d*A:=by dsimp [d,A]; rw [mul_assoc,← Real.rpow_add hp']; simp
   refine ⟨d*∑' i,w i,mul_nonneg (zero_le_one.trans hd) (tsum_nonneg (fun i=> (weight_pos a b i).le)),?_⟩
   intro r hr c z hc hz
   obtain ⟨n,hn,hn'⟩:=shift_exists r hr
   let τ:= Equiv.addRight n; have hτ(i:ℤ):τ i=i+n:=rfl
   let μ:=radius n / r
   have hμ:1/2 ≤ μ:=by apply (_root_.le_div_iff₀ hr).mpr; linarith only [hn']
   have hμ':μ ≤ 1:= by apply (_root_.div_le_one hr).mpr hn
   have hu(i:ℤ):radius (τ i)/r = radius i * μ:= by rw [hτ,radius_add,mul_div_assoc]
   have hw (e:ℝ)(i:ℤ) : ((2:ℝ)^e)^i=(radius i)^e:=by simp_rw [← Real.rpow_intCast,← Real.rpow_mul zero_le_two, mul_comm e _,Real.rpow_intCast_mul zero_le_two];rfl
   have H(i:ℤ): ‖z (τ i)‖≤ (c*d)*w i:= by
     have hm:0 ≤ radius i*μ:=by positivity [radius_pos i]
     rcases le_or_gt i 0 with hi|hi
     · rw [show w=weights a b from rfl,weights,if_pos hi,hw, mul_assoc]; apply (hz (τ i)).trans
       by_cases hf : radius (τ i)/r ≤ 1/4
       · rw [if_pos hf,hu]; exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hm (mul_le_of_le_one_right (radius_pos _).le hμ') ha.le) hc).trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (Real.rpow_nonneg (radius_pos i).le _) hd) hc)
       rw [if_neg hf]; apply mul_le_mul_of_nonneg_left _ hc
       exact (Real.rpow_le_rpow_of_nonpos hp' (not_le.mp hf).le (by linarith)).trans ((le_of_eq hA).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hp'.le (le_trans (hu i ▸ not_le.mp hf).le (mul_le_of_le_one_right (radius_pos i).le hμ')) ha.le) (by linarith only [hd])))
     rw [show w=weights a b from rfl,weights,if_neg (by omega),hw,mul_assoc]; apply (hz (τ i)).trans
     have hh : 1/4 < radius i*μ:= lt_of_lt_of_le (by linarith only [hμ]: (1/4:ℝ)<μ) (le_mul_of_one_le_left (by linarith) (by exact (by simpa only [radius,zpow_zero] using (zpow_le_zpow_right₀ (show 1≤(2:ℝ) from one_le_two) hi.le))))
     rw [if_neg (by rw [hu]; exact hh.not_ge),hu,Real.mul_rpow (radius_pos _).le (by positivity)]
     exact (mul_le_mul_of_nonneg_left (le_trans (Real.rpow_le_rpow_of_nonpos hp' (by linarith only [hμ]) (by linarith)) hda) (Real.rpow_nonneg (radius_pos _).le _)).trans (le_of_eq (mul_comm ..)) |> (mul_le_mul_of_nonneg_left · hc)
   have hh' : Summable (fun i=>‖z (τ i)‖):=by exact Summable.of_norm_bounded ((weights_sum ha hb).mul_left (c*d)) (fun i=>by simpa using H i)
   have hh'': Summable (fun i=>‖z i‖):=(τ.summable_iff).1 hh'
   refine ⟨hh'',(norm_tsum_le_tsum_norm hh'').trans (τ.tsum_eq (fun i=>‖z i‖)|>.symm.trans_le ?_)⟩
   exact (Summable.tsum_le_tsum H hh' ((weights_sum ha hb).mul_left _)).trans_eq (by rw [tsum_mul_left,mul_assoc])
end YM.Contacts
