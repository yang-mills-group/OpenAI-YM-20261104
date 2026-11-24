import YM.OPE.Compatible.Soup.Dune
/-!
# Measuring credit at all $β. Chamber rent
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant.Aloof
open Function Filter MeasureTheory Lattice Laurent Wilson Matrix RG Gauge Precision
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ENNReal ContDiff
open Eyrie Push Push.AbsoluteSums Push.Mark Cascade Flume Flume.Page Flume.Script Pilot Finset Sleeve
open Silt Libra Coin Rill Silt.Float Variance Votive PertExtension Series GaussianScore Radial Next.Foundations
variable {E I:Type} {k j:ℕ}
section
variable [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]
open Cinders Metric Set
variable (L:Law E)(μ:Measure E)[μ.IsAddHaarMeasure]
variable {a b c d r s t:ℝ} (hp:∀ x:E,d*‖x‖^2 ≤ L.P x x)(he:0<d)
omit [MeasurableSpace E] [BorelSpace E] in lemma wickG (f:E→L[ℝ] ℝ)(hp:∀ x:E,d*‖x‖^2 ≤ L.P x x)(hd:0 < d): L.wick f.toLinearMap f.toLinearMap ≤ ‖f‖^2/d:=by
        let x:=L.inverse f.toLinearMap; have hv:L.wick f.toLinearMap f.toLinearMap=f x:=rfl; rw [hv]
        by_cases h: x=0; rw[h,map_zero]; positivity
        have hZ : 0<‖x‖:= norm_pos_iff.mpr h; have hx:f x≤ ‖f‖*‖x‖:=(Real.le_norm_self _).trans (f.le_opNorm _); have hh : L.P x x=f x:=by unfold x; rw [L.applies]; rfl
        have hL:= hp x; rw[hh] at hL; apply hx.trans; calc
             _ ≤ ‖f‖*(‖f‖/d):=mul_le_mul_of_nonneg_left (by rw[le_div_iff₀ hd]; apply le_of_mul_le_mul_right _ hZ; exact (show ‖x‖*d*‖x‖=d*‖x‖^2 from by ring).trans_le (hL.trans hx)) (norm_nonneg _)
             _ =_ :=by ring
local notation "N!"=> Fin (Module.finrank ℝ E)
noncomputable def maxion (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]:=1+∑ i: Fin (Module.finrank ℝ E),‖Module.finBasis ℝ E i‖
lemma ionPositive (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] :0 < maxion E:=by unfold maxion; positivity
noncomputable abbrev WindB (i:N!): E →L[ℝ] ℝ:= ((Module.finBasis ℝ E).coord i).toContinuousLinearMap
noncomputable def Γθ (d:ℝ):ℝ:= ∑ i:N!,2*Real.exp (‖WindB (E:=E) i‖ ^ 2/d/2)
omit [MeasurableSpace E] [BorelSpace E] in lemma stern (x:E):‖x‖ ≤ ∑ i:N!,‖WindB (E:=E) i x‖*‖Module.finBasis ℝ E i‖:=by nth_rw 1 [← (Module.finBasis ℝ E).sum_repr x]; apply (norm_sum_le ..).trans; simp_rw[norm_smul]; exact le_rfl
include hp he
lemma gale (ht:0≤t): (quart L μ).real {x:E|maxion E*t<‖x‖} ≤ Γθ (E:=E) d*Real.exp (-t):=by
         let p(i:N!): Set E:={x|t<‖WindB i x‖}; have hx(i:N!) : (quart L μ).real (p i)≤ 2*Real.exp (‖WindB (E:=E) i‖^2/d/2)*Real.exp (-t):=(defeat L μ (WindB (E:=E) i).toLinearMap t).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_monotone (div_le_div_of_nonneg_right (wickG L (WindB i) hp he) (by norm_num))) (by norm_num)) (Real.exp_pos _|>.le))
         refine (measureReal_mono (s₂:=⋃ i,p i) ?_).trans ((measureReal_iUnion_fintype_le p).trans ((sum_le_sum (fun i _=>hx i)).trans (by rw[← Finset.sum_mul]; rfl))); intro x hh; rw[mem_iUnion]; by_contra h; push Not at h; exact (not_le.mpr (show maxion E*t < ‖x‖ from hh)) (le_trans (stern x) (le_trans (sum_le_sum (g:=fun i=> t*‖Module.finBasis ℝ E i‖) (fun i _=>mul_le_mul_of_nonneg_right (not_lt.mp (h i)) (norm_nonneg _))) (by rw [← Finset.mul_sum,mul_comm t]; apply mul_le_mul_of_nonneg_right _ ht; unfold maxion; exact le_add_of_nonneg_left zero_le_one))) -- rfl fix
noncomputable def hail (d:ℝ)(k:ℕ):ℝ := ∑ i:N!, (Real.sqrt (‖WindB (E:=E) i‖^2/d)*ampleP k)*‖Module.finBasis ℝ E i‖
lemma halo (hk:0 < k): Fault (quart L μ) k (fun x:E=> ‖x‖) (hail (E:=E) d k):=by
        let p(i:N!)(x:E):=‖WindB i x‖ * ‖Module.finBasis ℝ E i‖; let v(i:N!):= ‖WindB (E:=E) i‖^2/d; have h(i:N!): 0 ≤ v i:=by unfold v; positivity
        have hh(i:N!): Fault (quart L μ) k (p i) (Real.sqrt (v i)*ampleP k*‖Module.finBasis ℝ E i‖):=by
             let H:= (Lal L μ (WindB (E:=E) i).toLinearMap (Real.sqrt_nonneg (v i)) ((Real.sq_sqrt (h i)).symm ▸ wickG L (WindB i) hp he) hk).NormT; have he:=H.scaling ‖Module.finBasis ℝ E i‖; rw [norm_norm,mul_comm] at he; refine congr_arg (fun x:E→ℝ=> Fault (quart L μ) k x _) ?_ |>.mp he; ext x; exact mul_comm ..
        let f:=∑ i,p i; exact (Fault.sum Finset.univ p _ (fun i _=>hh i) hk).ofLe (continuous_norm.aestronglyMeasurable) (Eventually.of_forall fun i=>by change ‖‖i‖‖ ≤ ‖f i‖; unfold f; rw [norm_norm,Finset.sum_apply]; exact (stern i).trans (Real.le_norm_self _))
omit hp he
local notation "B!"=> μ.real (ball (0:E) 1)
lemma ballE (hr:0<r)(ht:∀ x∈ball (0:E) r,L.P x x ≤ 2*c) : (r^Module.finrank ℝ E * μ.real (ball (0:E) 1))* Real.exp (-c) ≤ rentF L μ :=by
       let S:= ball (0:E) r; have hs: MeasurableSet S:=isOpen_ball.measurableSet; have hK:μ S<⊤:=measure_ball_lt_top; have he : μ.real S=r^(Module.finrank ℝ E)*μ.real (ball (0:E) 1):=by unfold Measure.real S; rw [μ.addHaar_ball_of_pos _ hr, ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)]
       rw [←he,← show (∫ _ in S,Real.exp (-c) ∂μ)= μ.real S*Real.exp (-c) from setIntegral_const ..]; apply le_trans _ (setIntegral_le_integral (s:=S) (turnI ..) (Eventually.of_forall fun x=> (Real.exp_pos _).le)); exact setIntegral_mono_on (integrableOn_const hK.ne) ((turnI L μ).integrableOn) hs fun x hx=> Real.exp_monotone (show -c ≤ -(L.P x x) / 2 from by linarith only[ht x hx])
end
end YM.OPE.Merchant.Aloof
