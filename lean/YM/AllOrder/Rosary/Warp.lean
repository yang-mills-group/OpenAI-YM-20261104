import YM.AllOrder.Rosary.Repair
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Rosary
open Function Filter Set Lattice Wilson RG Ovens
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration Push.BetaTransport
open Till Burn
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ H w : ℝ}
    {X : Listing G n} {v : Collection.Source G n} {ι κ : Type}
/-! Pole & Estimate budgets billed after L. Coarse T.cost=up betaHat(s) or down exactly (for simplicity). -/
namespace Repair
open Push PriceCompiler Floe Floe.Step Floe.Pace Floe.StateE Floe.Step.PlanV Plateau PhysicalNext.Repeat Pressure
open ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.Blaze Catch Catch.Clock -- maybe remove
open Tilt
-- Cost ratio for nearby betas. Payout via Search lease. Includes weighted difference with all mask.Finance.
local notation "Z"=>Real.exp
-- wrap exponent pays after-L, with true periods at least cubically in bill_B. Gives constants explicitly.
open Asymptotics Lapis Gyro
variable {δ K α:ℝ}{A:Catch.Clock ι} {p:ι→BudgetPoint}{S':Stage}   -- scrub
structure Loft (B:BudgetPoint)(n:Side):Prop where
 sizes : 120*B.B^2≤ n.val
 roomy : 20<n.val
local notation "t"=> A.cost
local notation "T"=> A.rail
namespace Loft
variable (v:BudgetPoint)(hn:Loft v n)
include hn
lemma pole : v.B≤ pitch n v.B:= by
 have ht:=hn.sizes; have h:= wake v.B hn.roomy; have hf:= v.B_pos; by_contra! he; nlinarith only [ht,h,Nat.mul_le_mul_right (4*v.B+2) (Nat.succ_le_of_lt he),Nat.one_le_iff_ne_zero.mpr hf.ne',mul_self_le_mul_self (Nat.zero_le 1) hf]
lemma roof : n.val≤100*(pitch n v.B)^2:= by have hb:=hn.pole; have h:=wake v.B hn.roomy; have hv:=v.B_pos; nlinarith only [hb,h,Nat.mul_le_mul_left (pitch n v.B) hb,hv,mul_self_le_mul_self (Nat.zero_le 1) hv]
variable {v}
end Loft
variable {f g h:ι→ℝ}{n:ι→Side}
set_option quotPrecheck false
local notation "P"=> fun i:ι=> pitch (n i) (p i|>.B)
-- nectar supply.Meter
local notation "H"=> A.Meter
lemma climate (hw:Frost A S' p)(hp:∀ᶠ i in T, Loft (p i) (n i)): Tendsto P T atTop := tendsto_atTop_mono' _ (show ∀ᶠ i in T,radiusB (A.cost i)≤ P i from (hw.and hp).mono fun i hx=> (hx.1.2.1).symm ▸ hx.2.pole) (Work.E01.radiusB_tendsto.comp A.drive)
lemma ray (G:Gauge)(hw:Frost A S' p)(hp:∀ᶠ i in T, Loft (p i) (n i))(b:ℝ)(k:ℕ): H (fun i=> ((n i).val:ℝ)^k * Real.exp (-(2:ℝ)*P i)) b := by
 have hx:(fun x:ℝ=> ((100:ℝ)*x^2)^k / Real.exp (1*x))=ᶠ[atTop] fun x=> (100:ℝ)^k*((x^(2*k)) / Real.exp (1*x)):=Eventually.of_forall fun x=>by dsimp only; rw [mul_pow,pow_mul]; ring
 have hT : Tendsto (fun x:ℝ=> ((100:ℝ)*x^2)^k/Real.exp (1*x)) atTop (𝓝 0):= (show Tendsto (fun x:ℝ=> (100:ℝ)^k*((x^(2*k))/Real.exp (1*x))) atTop (𝓝 0) from (by convert! ((isLittleO_pow_exp_pos_mul_atTop (2*k) (zero_lt_one (α:=ℝ))).tendsto_div_nhds_zero).const_mul ((100:ℝ)^k) using 1; simp)).congr' hx.symm
 refine Meter.smaller (cool (G:=G) (fun i=> Real.exp (-(1:ℝ)*radiusB i)) (Plateau.dearth_rate G _ _ zero_lt_one b)) ?_
 filter_upwards [hw,hp,((hT.comp (tendsto_natCast_atTop_atTop.comp (climate hw hp))).eventually (ge_mem_nhds zero_lt_one))] with i hw hv hτ; rw [abs_of_nonneg (by positivity : 0≤ ((n i).val:ℝ)^k*Z (-(2:ℝ)*P i)),comp_apply, abs_of_pos (Real.exp_pos _), ← hw.2.1]; let N:= P i; let v : ℝ:= N; change (100*v^2)^k/Z (1*v) ≤ 1 at hτ; rw [div_le_one (Real.exp_pos _)] at hτ; change _ ≤ Z _; refine (mul_le_mul_of_nonneg_right ((show ((n i).val:ℝ)^k≤ _ from pow_le_pow_left₀ (Nat.cast_nonneg _) (by dsimp only [v,N]; exact_mod_cast hv.roof : ((n i).val:ℝ) ≤ 100*v^2) _).trans hτ) (Real.exp_nonneg _)).trans ?_;
 rw [← Real.exp_add]; have he:N=P i:=rfl; exact Real.exp_monotone (by change 1*v+-(2:ℝ)*v≤ -(1:ℝ)*(p i).B; linarith only [show (p i).B ≤ v from Nat.cast_le.mpr hv.pole]) -- casting
lemma wrap_hard (G:Gauge)(hw:Frost A S' p)(hp:∀ᶠ i in T, Loft (p i) (n i))(hf:H f δ)(hg: ∀ᶠ i in T,|g i|≤ reward (n i) (p i|>.threshold)*vault (n i) (p i) (f i))(k:ℕ)(b:ℝ): H (fun i=> (p i|>.threshold)^2*Z (((p i).supportExponent+1)*P i)*g i*((n i).val:ℝ)^k) b:= by
 let u:= (ray G hw hp (b-δ) (k+10)); let C:= u.mul hf|>.lscale 3; refine (C.weak (by linarith)).smaller ?_; filter_upwards [hg] with i hi; let x:= p i; let y:= (n i); let t':ℝ:=P i; let s :ℝ:=x.supportExponent+1; have ht:= x.threshold_pos; let v':= Z (s*t'); let F:=(y.val:ℝ); have hF : 0 ≤ F:= by unfold F; positivity
 let Q:= Z ( -preExponent x * t'); have hh:f i≤|f i|:= le_abs_self _; let B:= x.threshold^2*v'; have hb:0≤B:=by unfold B v'; positivity
 change |B*g i*F^k| ≤|3*(F^(k+10)*Z _ *f i)|;
 simp only [abs_mul,abs_of_nonneg hb,abs_of_nonneg (pow_nonneg hF k),abs_of_nonneg (pow_nonneg hF (k+10)), abs_of_nonneg (Real.exp_nonneg _),abs_of_nonneg (by norm_num : (0:ℝ) ≤3)]
 apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi hb) (pow_nonneg hF _)); unfold reward vault; change B*((3/x.threshold^2*F^10)*(f i*Q))*F^k≤_; calc
   _ ≤ B*((3/x.threshold^2*F^10)*(|f i| *Q))*F^k:= by unfold Q; gcongr
   _ ≤ _:= le_of_eq (by
      have hY:v'*Q=Z (-(2:ℝ)*t'):=by unfold v' Q; rw [← Real.exp_add]; unfold s preExponent; apply congr_arg Real.exp; ring
      change B*((3/x.threshold^2*F^10)*(|f i| *Q))*F^k=3*(F^(k+10)*Z (-(2:ℝ)*t') * |f i|) -- equality instead
      unfold B; rw [← hY,pow_add]; field_simp)
end Repair
end YM.AllOrder.Rosary
