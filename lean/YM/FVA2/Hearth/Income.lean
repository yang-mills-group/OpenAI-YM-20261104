import YM.FVA2.Hearth.Threshold
/-!
# Haar checking at fixed finite geometry for conditional ray formulas

Not to be confused with `Route.Bulk.income`. Here establish some fixed-geometry
continuity and integrability results, e.g. a cutoff estimate and a use of steepness
for these `Tracks`. Not claiming a uniform epoch estimate.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Hearth
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter Set MeasureTheory Metric PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade RGComparison.Core16
open scoped Classical Topology BigOperators ContDiff

variable {G:Gauge}{n:Side}{L:Fabric G n}(T:Cloth L)(w:L.Accounts→ℝ→ℝ)(y:Flats G (Bottom L))
variable {J:ChartRatio G}
local notation "μ" => Chart.physical G (Warm T)
local notation "F"=> Facade.Panel T
local notation "X"=> (Warm T→ G.El)
local notation "ν"=> tangent G (Warm T)
local notation "Δ"=> Module.finrank ℝ (Facade.Panel T)
local notation "a"=> Facade.raise (Facade.rate T) w y

-- fuel relative to full Wilson kernel (up to g and i constants from thermostat.S.Warn).
 def fuel (u: ℝ)(x: Warm T→ G.El) : ℝ:= Real.exp (-(u^2+front T w y u x)/u^2)
 def income (O:Wilson.Config G n→ℝ)(u:ℝ)(x:Warm T→ G.El): ℝ:= attending L O (committed T y u x)* fuel T w y u x
 lemma postage (r:ℝ) : Measurable (front T w y r):= (L.measurable_cost _).comp ((committed_cont T y).comp (continuous_const.prodMk continuous_id)).measurable

variable (O:Wilson.Config G n→ℝ)(hO: PreTest O)
-- actual observable on FULL top chart. gauge statement not assumed outside PreTest
 def seed (O:Wilson.Config G n→ℝ)(u:Flats G n): ℝ:= O (Orb.liftLinks (expLinks G _ u))
include T in
lemma certified (h:PreTest O) : ContDiffAt ℝ ∞ (seed O) 0:= OpenSlots.covariant T h -- include T
local notation "V" => seed O ∘ line T
 def stipend (J:ChartRatio G) : ℝ × Facade.Panel T→ℝ := coat y (jacobian J) (seed O ∘ line T)
local notation "g₂"=> Hearth.stipend T y O J
 def wages : ℕ→ℝ:= Therm.stamp ν (g₂) (a) 1

include hO
lemma income_meas (r): Measurable (income T w y O r):= ((eligible L hO).reading.meas.comp ((committed_cont T y).comp (continuous_const.prodMk continuous_id)).measurable).mul (Measurable.exp (((measurable_const.add (postage T w y r)).neg).div_const _))
include J
omit J hO in
lemma flowed (v:F)(u:ℝ): attending L O (committed T y u (expLinks G _ v)) = (seed O ∘ line T) ((flank y) (u,v)):= by
 unfold attending committed seed; simp only [Function.comp_apply]; rw [attend_main]; rfl
lemma pay_flow (hj:LocalRatio J): Measurable (g₂) := by
 refine ((Ratio.jacobian_meas hj).comp measurable_snd).mul ?_; exact hO.continuous.measurable.comp (((Orb.lift_cont G).measurable.comp expLinks_meas).comp ((LinearMap.toContinuousLinearMap (line T ∘ₗ (flank y))).continuous.measurable))
lemma hot (hj:LocalRatio J) : ContDiffAt ℝ ∞ (g₂) 0:= by
 let L':= line T ∘ₗ (flank y)
 apply (show ContDiffAt ℝ ∞ (jacobian J (U:=Warm T) ∘ LinearMap.snd ℝ ℝ F) 0 from (leaned _ (Ratio.jacobian_smooth hj)).of_le le_top).mul ?_
 exact (show ContDiffAt ℝ ∞ (seed O) (L' 0) from by rw [map_zero]; exact certified T O hO).comp _ (LinearMap.toContinuousLinearMap L').contDiff.contDiffAt
omit J
omit hO in
lemma raised (hh:∀ i,Measurable (w i)) : Measurable (a):= by
 let q : ℝ × F → ℝ × X := fun z=> (z.1, expLinks G _ z.2)
 let b := uncurry (committed T y) ∘ q
 have hx: Measurable (fun z:ℝ × F=> q z):= measurable_fst.prodMk (expLinks_meas.comp (measurable_snd (α:=ℝ) (β:=F)))
 have he: Measurable b:= (committed_cont T y).measurable.comp hx
 let d (i:L.Accounts)(x:ℝ × F):= w i x.1 * L.price (b x) i
 have hD (i:L.Accounts): Measurable (d i):= ((hh i).comp (measurable_fst (α:=ℝ) (β:=F))).mul ((L.price_clean i).comp he)
 have hp: Measurable (fun x:ℝ × F=> (∑ i,d i x)):= Finset.measurable_fun_sum _ fun i _ => hD i
 have ha: (Facade.raise (Facade.rate T) w y) = Therm.pedal + fun x:ℝ × F=> ∑ i,d i x:= funext fun ⟨r,x⟩=> truePrice T w y r x
 rw [ha]; exact Therm.pedal_smooth.continuous.measurable.add hp

local notation "Iₗ"=> income T w y O
variable (hj:LocalRatio J)
include hj J
lemma presentation {r t:ℝ}(ht:0<t)(hm: r<Chart.small G J)(hr:0<r):
 (t^Δ)⁻¹ * ∫ x in chamber G (Warm T) r,Iₗ t x ∂μ= Therm.chartLine ν g₂ a 1 t r:= by
 rw [Ratio.chamber_integral hj (Iₗ t) (income_meas T w y O hO _) hm hr, show (t^Δ)⁻¹ = StationaryMarks.scale G (Warm T) t from rfl, StationaryMarks.in_scale ht]; unfold Therm.chartLine; apply setIntegral_congr_fun (disc_meas ..); intro x hx
 dsimp only; rw [projection_eq]; change _= (jacobian J (t • x)* V (_))*Real.exp (-(a (t*1,t•x))/t^2); unfold income fuel; rw [flowed T y O, mul_one, truePrice];
 rw [mul_assoc]; congr 2; rw [show t•((1:ℝ),x) = (t,t•x) by rw [Prod.smul_mk]; simp]
omit hj J

lemma paid (u:ℝ)(h:∀ i,0<w i u): Integrable (Iₗ u) μ:= by
 obtain ⟨v,hv⟩:= (eligible L hO).reading.bounded; apply (integrable_const v).mono' (income_meas _ _ _ _ hO u).aestronglyMeasurable (Eventually.of_forall fun x=>?_)
 have hh: fuel T w y u x≤1:= Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (add_nonneg (sq_nonneg _) (L.nonneg_cost h _))) (sq_nonneg _)); unfold income;
 rw [norm_mul, Real.norm_of_nonneg (show 0≤ fuel T w y u x from (Real.exp_pos _).le)]
 exact (mul_le_of_le_one_right (norm_nonneg _) hh).trans (hv _)

include hj J
variable (hu:∀ i,ContinuousAt (w i) 0)(hv:∀ i,0< w i 0)
include hu hv
lemma cutoff {r:ℝ} (he: r≤Chart.small G J)(hr:0<r) (k:ℕ): Bill k (fun t=> (t^Δ)⁻¹ * ∫ x in (chamber G (Warm T) r)ᶜ,Iₗ t x ∂μ):= by
 let S:=chamber G (Warm T) r; have hs:IsOpen S := Ratio.chamber_open hj he
 obtain ⟨b,hb,H⟩:= uniformFront T y w hu hv S hs (fun i _=>⟨0,mem_ball_self hr,G.mat_lieExp_zero⟩)
 obtain ⟨R,hR,h⟩:= rapid hb (Δ) k
 obtain ⟨v,hv⟩:= (eligible L hO).reading.bounded; have vn:0≤v:= le_trans (norm_nonneg _) (hv 1)
 refine ⟨v*R,by positivity,?_⟩; filter_upwards [H.filter_mono nhdsWithin_le_nhds,Tested.eventually_pos] with t he ht
 let z:=v* Real.exp (-b/t^2); have hz:0≤z:= by unfold z; positivity
 have hx : ‖∫ x in Sᶜ,Iₗ t x∂μ‖ ≤ z:= by
   have hi:Integrable (fun _:X=>z) μ:= integrable_const z
   apply (norm_integral_le_of_norm_le (g:=fun _=> z) hi.integrableOn ?_).trans ((setIntegral_le_integral hi (Eventually.of_forall fun _=>hz)).trans_eq (by simp)); filter_upwards [ae_restrict_mem hs.measurableSet.compl] with x hw
   unfold income fuel; rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]; exact mul_le_mul (hv _) (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg ((he _ hw).trans (le_add_of_nonneg_left (sq_nonneg _)))) (sq_nonneg _))) (Real.exp_pos _).le vn
 rw [norm_mul, Real.norm_of_nonneg (by positivity : 0≤(t^Δ)⁻¹)]
 exact (mul_le_mul_of_nonneg_left hx (by positivity)).trans (by unfold z; rw [mul_left_comm,mul_assoc]; exact mul_le_mul_of_nonneg_left (h t ht) vn)

-- full asymptotic power reading from literal Wilson thermostat-normalized conditional
-- (before dividing by ANY vacuum constant, up to overall powers, exp(-1), and entire thermostat)
 def Burn (t:ℝ) := (t^Δ)⁻¹ * ∫ x,Iₗ t x ∂μ

theorem aspirations (hh:Laplace.Steep (a))(hM:∀ i,Measurable (w i)): Tracks (Burn T w y O) (constit T w y J V):= by
 rw [constit,Tracks,Tracks.asTerm]; intro k
 have hθ:= hh.toStationary.rescale_estimate (Therm.screen ν 1) (hot T y O hO hj) (pay_flow T y O hO hj) (raised T w y hM) hh.gap k
 obtain ⟨d,hd,h⟩:= hθ
 let r:= min d (Chart.small G J)/2; have hz:0<r:= half_pos (lt_min hd (Ratio.small_pos hj)); have he : r < min d (Chart.small G J):= half_lt_self (lt_min hd (Ratio.small_pos hj)); have h' := he.trans_le (min_le_right ..)
 obtain ⟨M,hM,H⟩:= cutoff T w y O hO hj hu hv h'.le hz (k+1)
 obtain ⟨D,hD⟩:=h r ⟨hz,he.trans_le (min_le_left ..)⟩
 have hc:∀ᶠ t in Tested.germ,∀ i,0< w i t:= eventually_all.mpr fun i=> ((hu i).tendsto.mono_left nhdsWithin_le_nhds).eventually (eventually_gt_nhds (hv i))
 refine ⟨|D|+M,by positivity,?_⟩; filter_upwards [H,hD,hc,Tested.eventually_small hz] with t h₁ h₂ ht ⟨ht₀,ht'⟩
 let S:=chamber G (Warm T) r
 have hu:Burn T w y O t = Therm.localFull ν g₂ a 1 t r + ((t^Δ)⁻¹ * ∫ x in Sᶜ,Iₗ t x ∂μ):= by
     unfold Burn; rw [Therm.local_chartLine ν g₂ a (t:=t) (x:=1) (r:=r) ht₀.le (by simpa using ht'), ← presentation T w y O hO hj ht₀ h' hz, ←mul_add,integral_add_compl ((Ratio.chamber_open hj h'.le).measurableSet) (paid _ _ _ _ hO t ht)]
 rw [Pi.sub_apply,hu,add_sub_right_comm]; apply (norm_add_le ..).trans ((add_le_add ?_ h₁).trans_eq (add_mul ..).symm)
 exact le_trans h₂ (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
end YM.FVA2.Hearth
