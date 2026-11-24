import YM.Integration.WilsonCapturedPrimaryPointFiledWindow
import YM.Integration.WilsonPhysicalProjectionFiledCover
import YM.Integration.WilsonPhysicalProjectionHalo
import YM.Integration.OriginalPeriodWindingPrice

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryPointStage
open Filter Function Finset Lattice Laurent Wilson RG Precision FormalBulk08
open Next.Free Flat Stationary Kemp Pose Gorge Reef Mesa Exterior
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open PhysicalNext.Repeat.Legato Next.Foundations RG16 RG16.Literal RG16.Guarding
open Pert.Asymptotics Trace.Physical
open WilsonCapturedPrimaryPointBasis WilsonCapturedPrimaryPointWindow WilsonPointChildFiledPress
open scoped Classical BigOperators Topology ENNReal
variable {G:Gauge}{d D:ℕ}

theorem side (R:Run G) (simple:G.Simple):
    ∀ᶠ i:ℕ in atTop,∀N per:ℕ,i≤N →
      2*(R.family.path.rep N per i).p.B<(R.family.side i per).val:=by
  filter_upwards [OriginalPeriodWindingPrice.period_power R.family.path.levels 3,
    (Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop 4] with i period hot
  intro N per live
  let b:=R.family.path.levels.clock.hatBeta i
  have b4:4≤b:=hot
  have b1:1≤b:=by linarith only [b4]
  have above:(Real.log b)^2≤b^2:=pow_le_pow_left₀ (Real.log_nonneg b1) (Real.log_le_self (zero_le_one.trans b1)) _
  let B:=(R.family.path.rep N per i).p.B
  have actual:(R.family.path.rep N per i).p=R.alloy.B.a.budget i:=(R.makes.wilson.represents N per i live).vac
  have high:(B:ℝ)≤(Real.log b)^2+1:=by
    dsimp only [B];rw [actual]; exact (Nat.ceil_lt_add_one (sq_nonneg _)).le
  have xx:1<b^2:=one_lt_pow₀ (by linarith only [b4]) (by norm_num)
  have cube:=mul_le_mul_of_nonneg_right b4 (sq_nonneg b)
  have room:=period per
  change b^3≤((R.family.side i per).val:ℝ) at room
  have net:(2:ℝ)*B<((R.family.side i per).val:ℝ):=by nlinarith only [high,above,xx,cube,room]
  exact_mod_cast net


theorem quarter (w:ℝ)(hw:0<w)(s:ℕ):
    widthCost (w/2/2) s+widthCost (w/2) s≤((2:ℝ)^s+1)*widthCost (w/2) s:=by
  have base : 1+((s:ℝ)+1)/(w/2/2)≤2*(1+((s:ℝ)+1)/(w/2)):=by
    field_simp; nlinarith only [hw]
  have hh:=pow_le_pow_left₀ (by positivity : 0≤1+((s:ℝ)+1)/(w/2/2)) base s
  simp only [mul_pow] at hh
  simpa [widthCost,Nat.cast_add,Nat.cast_one,add_mul] using add_le_add_right hh ((1+((s:ℝ)+1)/(w/2))^s)

theorem original (R:Run G)(L:Primer.Families R.family)(a:G.ColorIndex)(depth:d<D)
    (simple:G.Simple)(funded:WilsonPointChildFiledTest.Filed R){u:ℕ→ℕ}
    (announced:WilsonWindowFormalPurchase.Canonical u R.kit)(o:Loc G 1)
    (Q r target:ℕ)(row:(R.family.labels.level d).Index):
    ∀ᶠi:ℕ in atTop,∀N per:ℕ,i≤N→∀t:Tour R i,∀c:(R.family.labels.level d).Index,∀e≤Q,
      let F:=R.family.labels.level d
      let B:=(R.family.path.rep N per i).p.B
      let n:=R.family.side i per
      let Z:=WilsonOlderFreshPointGauge.field R L a depth i (axis F c) (t,fixed D)
      |quote F B (sieve n (Z e r)) (axis F row)-pearlJ F (Z e r) row|≤
        (regulatorRun R.family N per i)^target:=by
  let F:=R.family.labels.level d
  let s:=d*(F.grades row).2
  obtain ⟨K,K0,field⟩:=WilsonCapturedPrimaryPointFiledWindow.original R L a depth simple funded
    o Q r row (η:=1) zero_lt_one
  let C:=K*((2:ℝ)^s+1)*(2*‖fixed D‖)
  have C0:0≤C:=by dsimp [C];positivity
  have cost:=WilsonPhysicalProjectionFiledCover.width_charge R simple announced s 0 C0 zero_lt_one
  filter_upwards [field,cost,side R simple,WilsonPhysicalProjectionHalo.original R simple announced
    (target+2),(Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop (2:ℝ)] with i priced charge unwrapped wrap warm
  intro N per here t c e he _ B n Z
  let w:=width R i
  let g:=regulatorRun R.family N per i
  let β:=R.family.path.β N per i
  have wp:0<w:=(Primer.FamilyWindow R.family).pos _
  have band:=(R.makes.wilson.represents N per i here).band.1
  change R.family.path.levels.clock.hatBeta i/2≤β at band
  have bp:0<β:=by linarith only [band,warm]
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr bp)
  have ht:0≤R.family.path.levels.clock.hatBeta i:=by linarith only [warm]
  have bi:(g⁻¹)^2=β:=by change (((Real.sqrt β)⁻¹)⁻¹)^2=β;rw [inv_inv,Real.sq_sqrt bp.le]
  have hot:R.family.path.levels.clock.hatBeta i≤2*(g⁻¹)^2:=by rw [bi];linarith only [band]
  have prev:(((B-1:ℕ):ℝ))≤(B:ℝ):=by exact_mod_cast Nat.sub_le B 1
  have H:=mul_le_mul_of_nonneg_left prev wp.le
  have hd: -w*(B:ℝ)/2≤ -(w/2)*((B-1:ℕ):ℝ):=by linarith only [H]
  have decay:Real.exp (-w*(B:ℝ)/2)≤g^(target+3):=
    (Real.exp_le_exp.mpr hd).trans (wrap N per here).2
  have inverse:(w/2)⁻¹≤2*(WilsonPhysicalHistoryAperture.width R.family i)⁻¹:=by
    change (w/2)⁻¹≤2*w⁻¹;rw [inv_div];simp [div_eq_mul_inv]
  have half:=charge N per here (w/2) (half_pos wp) inverse
  have localbill:widthCost (w/2) s*C≤g⁻¹:=by
    simpa only [pow_zero,mul_one,Real.rpow_neg_one] using half
  have weight:0≤widthCost (w/2) s:=by unfold widthCost;positivity
  have ph:=((priced t c e he).2 n B (unwrapped N per here))
  have large:=mul_le_mul_of_nonneg_left (quarter w wp s) K0
  have betaScale:=mul_le_mul_of_nonneg_right hot (norm_nonneg (fixed D))
  have sourced:=mul_le_mul betaScale decay (Real.exp_pos _).le (by positivity)
  have step:=mul_le_mul large sourced (mul_nonneg (mul_nonneg ht (norm_nonneg _)) (Real.exp_pos _).le)
    (mul_nonneg K0 (mul_nonneg (by positivity) weight))
  calc
    _ ≤ K*(widthCost (w/2/2) s+widthCost (w/2) s)*
        ((R.family.path.levels.clock.hatBeta i*‖fixed D‖)*Real.exp (-w*(B:ℝ)/2)):=by
          simpa only [Real.rpow_one] using ph
    _ ≤ _ := step
    _ = (widthCost (w/2) s*C)*((g⁻¹)^2*g^(target+3)):=by dsimp only [C];ring
    _ ≤ g⁻¹*((g⁻¹)^2*g^(target+3)):=mul_le_mul_of_nonneg_right localbill (by positivity)
    _ = g^target:=by rw [pow_add];field_simp

end YM.Integration.WilsonCapturedPrimaryPointStage
