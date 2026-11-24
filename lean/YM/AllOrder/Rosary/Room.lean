import YM.AllOrder.Rosary.Bill
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
open Push PriceCompiler Floe Floe.Step Floe.StateE Floe.Step.PlanV Plateau PhysicalNext.Repeat Pressure
open ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.Blaze Catch Catch.Clock -- maybe remove
open Tilt
-- Cost ratio for nearby betas. Payout via Search lease. Includes weighted difference with all mask.Finance.
local notation "Z"=>Real.exp
namespace PostP
open Guard Lapis Gyro Time
variable (G)(p:Stage) -- stage real
variable (u:ℕ)
variable (H H':ℝ)
set_option quotPrecheck false
local notation "S"=> Sigma (Actor G p u H)
local notation "T"=>clockI.stage (Actor G p u H)
local notation "P"=> fun i:S=> (Actor.p i.2)
local notation "TV"=> fun i:S=> (P i|>.threshold)
local notation "N"=> fun i:S=>(Actor.n i.2)
local notation "X"=> fun i:S=> (Sigma.fst i)
local notation "a"=> fun i:S=> Actor.b i.2
local notation "b"=> fun i:S=> Actor.c i.2
local notation "Z₀"=> fun i:S=> Actor.D i.2
local notation "Δ"=> fun i:S=> Actor.Δ' i.2
local notation "k"=> fun i:S=> Actor.W i.2
local notation "U"=> fun i:S=> Actor.Δ i.2
local notation "Yξ"=>fun i:S=> C' (P i) G u (b i) (X i)
local notation "Y"=> fun i:S=> Actor.H' i.2
local notation "Q0"=> fun i:S=> θ1 G p (X i) u
local notation "M"=>Catch.Clock.Meter T
local notation "r"=> Catch.Clock.rail T
local notation "τ"=> Burn.credit u
lemma rents : ∀ᶠ i:S in (T).rail,(P i).threshold^2* |a i-b i| ≤ θ2 G p (X i) u:= by
 let C:= Time.credit G p; have hv:0 < C:= Time.credit_pos G p; let h:= (power_warp G p u H (τ-1)|>.2.2).lscale C⁻¹; filter_upwards [ h _ (by linarith : τ-1<τ)] with i hi; have he:= i.2.guess; let B:= P i; let Y':= a i; let s:= b i; let z:= Δ i; let y:= Z₀ i; let x:= X i; have hu: y-z=Y'-s:= (by change y- z= _; have hp:z=y-(Y'-s):=i.2.struck; linarith); change _* |Y'-s| ≤ _; rw [← hu]; have hh:B.threshold^2* |z| ≤ C* x^τ:= by
   refine (le_trans («b»:=C*(C⁻¹*((P i).threshold^2* |z|))) ?_ (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hi) hv.le)); rw [mul_inv_cancel_left₀ hv.ne'];
 apply le_trans (mul_le_mul_of_nonneg_left (abs_sub ..) (sq_nonneg B.threshold)); change B.threshold^2*(|y| + |z|)≤2*(C*x^(τ)); linarith only [show B.threshold^2* |y| ≤ C*x^τ from he,hh]
lemma certain : Compare T b a (τ+1):= by
 refine ⟨Eventually.of_forall fun i=> ⟨i.2.bright.2.1,i.2.bright.1⟩,?_⟩; refine (((θ1_meter G p u H|>.lscale 2).mul ((Repair.unwarp G (legal G p u H)).pow 2)).weak ?_).smaller ?_; · norm_num
 filter_upwards [rents G p u H] with i hi; let a':= TV i; have ha:0<a':=(P i).threshold_pos; rw [abs_sub_comm]; refine le_trans ?_ (le_abs_self _); change _ ≤(2*Q0 i)*(a'⁻¹)^2; rw [inv_pow,← div_eq_mul_inv, le_div_iff₀ (sq_pos_of_pos ha),mul_comm]; exact hi
local notation "T₂"=> fun i:S=> taxes (P i) G u (b i) (a i) (X i)
local notation "E"=> p.supportExponent
local notation "D₀"=> θ2 G p
local notation "Y₁"=> rentsAux p G
private lemma fiscal : ∀ᶠ i:S in r, Checks G p u H i.2:= by
 let T' := T; let q:=r; let hQ:= rents G p u H; let h:= (Compare.pledge G p (certain G p u H) (legal G p u H) (Burn.horizon u) (Age.scope (Burn.horizon u+2))); have ht': M T₂ (τ-1):= h.weak (by linarith); let A:= X
 let hγ:= power_warp G p u H (τ-1); let h𝒴:= Time.credit_pos G p; let hμ:= Time.authorized G p; let hr:= earns u; let C:=fun i:S=> Z (p.supportExponent)*(T₂ i)+food G (N i) (P i) (Δ i); let hp: M (fun i=> 2*C i) (τ-1):= ((ht'.lscale (Z E)).add hγ.1).lscale _; let hP:= (growth G p u H (β:=a) (Eventually.of_forall fun i=> i.2.bright.1)).lscale (Real.exp p.supportExponent)
 let hδ:=Meter.pale T τ; let H':=(θ1_meter G p u H).lscale 2; let hu(i:S):= D₀ (X i) u*(TV i)⁻¹^2; have hv:M hu (τ+1):=(H'.mul ((Repair.unwarp G (legal G p u H)).pow 2)).weak (by norm_num); let hw:=(((Meter.pale T (-(7/5:ℝ))).add (hδ.weak hr)).rscale 32); let hω:M (fun i=>(1+(radiusB (A i):ℝ))^4) 0:=(((Meter.const T 1).add (Repair.cool (G:=G) _ Rate.radius_price)).pow 4).weak (by norm_num)
 let hv':= hω.mul (Repair.warmth G (legal G p u H))
 have hk:= (hγ.2.1.weak (by linarith only [hr] : τ-1≤ -(2/5:ℝ))).add ((Meter.pale T (-(2/5:ℝ))).add (((hω.lscale (Time.softCeiling G p H)).unitPay le_rfl (Repair.warmth G (legal G p u H))).weak (by norm_num : -(1/2:ℝ)≤ -(2/5:ℝ))))
 filter_upwards [hQ,hp τ (by linarith),hv.low (by linarith) zero_lt_one,hP _ (by norm_num : -(3/2:ℝ)< -(7/5:ℝ)),hw _ (by norm_num : -(7/5:ℝ)< -(11/10:ℝ)),hk _ (by norm_num : -(2/5:ℝ)< -(1/3:ℝ)),T'.positive] with i hQ hp hv hP hw hk he
 let x:= A i; let B:= P i; have hx:0<x:=he; let k':=θ1 G p x u; have he:= Real.rpow_pos_of_pos hx τ; have ht:=B.threshold_pos; let y:=x^τ; have h𝕂: B.supportExponent=p.supportExponent:= i.2.frost.1.2.2; have hy: B.B=radiusB x:= i.2.frost.2.1; let d:= D₀ x u; have hd : 0≤d:=by change 0 ≤ 2*(Time.credit G p*y); unfold y; change 0 ≤ 2*(Time.credit G p*x^τ); positivity
 have he' : d≤ B.threshold^2:= by apply le_of_mul_le_mul_right («a»:=(B.threshold^2)⁻¹) ?_ (inv_pos.mpr (sq_pos_of_pos ht)); rw [mul_inv_cancel₀ (sq_pos_of_pos ht|>.ne'), ← inv_pow]; exact (le_abs_self _).trans hv.le
 refine ⟨hQ, ?_, ?_, (le_div_iff₀ (by norm_num)).mpr ((le_abs_self _).trans hw),?_⟩
 · have hj: Z (p.supportExponent)*T₂ i=Z B.supportExponent*T₂ i:=h𝕂 ▸ rfl; have hr: Time.base G p* Time.credit G p≤ (64:ℝ)⁻¹:= hμ.2; change rentsAux p G B x _ _ _ _ _ ≤ _; unfold rentsAux; change _+ (_+regularNeed G B p.clip p.width p.paths 0 d) ≤ y; rw [Time.table G p i.2.frost.1]; rw [h𝕂,abs_zero,zero_mul,mul_zero, add_zero]; have hv:= mul_le_mul_of_nonneg_right hr he.le; unfold d θ2 θ1 young; linarith only [show 2*(Real.exp E*taxes B G u (b i) (a i) x + food G (N i) B (Δ i)) ≤ x^τ from (le_abs_self _).trans hp,hv,he,show x^τ=y from rfl] -- linarith constants maybe expansions with parentheses
 · change Z B.supportExponent*_≤_; rw [h𝕂]; exact (le_abs_self _).trans hP
 have hf := Time.soft_table G p (p:=B) i.2.frost.1 i.2.bright.2.2.1 hd he'; rw [hy] at hf; refine le_trans (add_le_add_right (add_le_add_right hf _) _) ((le_abs_self _).trans hk)
theorem backed : ∀ᶠ x in atTop, ∀ i:Actor G p u H x, Checks G p u H i:= (clockI.everybody _).1 (fiscal G p u H)
end PostP
end Repair
end YM.AllOrder.Rosary
