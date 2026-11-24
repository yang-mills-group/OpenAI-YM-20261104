import YM.AllOrder.Rosary.Warp
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
open Asymptotics Lapis Gyro Guard
variable {δ K α:ℝ}{A:Catch.Clock ι} {p:ι→BudgetPoint}{S':Stage}
local notation "t"=> A.cost
local notation "T"=> A.rail
variable {f g h k u d:ι→ℝ}{n:ι→Side}
local notation "H"=> A.Meter
set_option quotPrecheck false
local notation "w"=> fun i:ι=> (p i).threshold
local notation "X"=> S'.clip
local notation "c!"=> S'.paths
local notation "c'"=> S'.paths
local notation "σ"=> S'.width
local notation "q"=> Time.probe S'
variable (hw:Frost A S' p) (G)
include hw
include G
lemma warmth : H w (-(1/2:ℝ)):= (cool (G:=G) (A:=A) _ Burn.temp_rate).eq_mem (hw.mono fun i hi=>hi.2.2.symm) -- include G
lemma unwarp : H (fun i=> (w i)⁻¹) (1/2:ℝ):= by
 refine Meter.smaller (Meter.pale A (1/2)) ?_; filter_upwards [hw,A.positive] with i hi hI; simp_rw [abs_of_nonneg (by positivity : 0≤ (A.cost i) ^ (1/2:ℝ)),← Real.sqrt_eq_rpow]; rw [abs_of_pos (inv_pos.mpr (p i|>.threshold_pos)), hi.2.2,temp]; let x:=A.cost i; have hv:0<Real.sqrt x:=Real.sqrt_pos.mpr hI; change (((Real.sqrt x)⁻¹)*Real.exp ((Real.log (Real.log x))^2))⁻¹≤ Real.sqrt x; apply le_trans (b:=((Real.sqrt x)⁻¹)⁻¹) (inv_anti₀ (inv_pos.mpr hv) (le_mul_of_one_le_right (inv_pos.mpr hv|>.le) (Real.one_le_exp (by positivity)))) (by simp)
local notation "qp" => pearl (Time.probe S')
abbrev rp (p:BudgetPoint)(G:Gauge):ℝ:= ((2:ℝ)⁻¹*∑ x:PlaqAxes, ∑ y:PlaqAxes,|kappa x y| * pairBill G p)
lemma price_table : ∀ᶠ i in A.rail,
 lowBase G X (pearl (p i)) σ c' = lowBase G X qp σ c' ∧ highBase G (pearl (p i)) σ c'=highBase G qp σ c'∧ turnFee (p i) = turnFee (q) ∧ (p i).supportExponent=S'.supportExponent ∧
 (∀ k,priceR G (p i) k= |k| * rp (q) G * (w i)^2)∧ (∀ k, repu G (p i) k= |factor*k| * rp (q) G * (w i)^2):= by
 filter_upwards [hw] with i hx; obtain ⟨⟨hv,hq,h⟩,-⟩:= hx; have hr: pairBill G (p i)= pairBill G q:= by unfold pairBill Time.probe; dsimp only []; rw [hv,hq]
 refine ⟨?_,?_,?_,h,?_,?_⟩
 · unfold lowBase anchoredFee lowFee pearl preExponent Time.probe lowCost rowCost faceCost pairBill rowDegree; dsimp; rw [hv,hq,h]
 · unfold highBase anchoredFee Geo.both highFee pearl preExponent Time.probe; dsimp; rw [hv,hq,h]
 · unfold turnFee Time.probe; dsimp; rw [hv,hq]
 · intro k; unfold priceR rp; rw [hr]; simp only [mul_assoc,Finset.sum_mul]
 intro k; unfold repu rp; rw [hr]; simp only [mul_assoc,Finset.sum_mul]
-- Frost.Guard totalFee with parameter table. bound δ outputs for moment-case.Clock.Meter related.HQ costs constants post.
lemma total_panel (hk:H k 0)(hu:H u 0)(hv:H f 0)(hh:H h 0) : H (fun i=> totalFee (p i) G X σ c' (k i) (u i) (f i) (h i)) 0:= by
 let u':=fun i:ι=> Z ((S'.supportExponent+3)*(↑(1:ℕ):ℝ)); let hf:= hv.rscale (Z ((S'.supportExponent+3)*(↑(1:ℕ):ℝ))); let hw:=warmth G hw; let z : H w 0:= hw.weak (by norm_num); have ht(i:ℕ):H (fun j=> w j^i) 0:= (z.pow i).weak (by simp); let f' i:= u i; let hx:= ((hu.ab.lscale factor).unitPay (le_refl (0:ℝ)) (ht 2)).lscale (turnFee q) |>.rscale (lowBase G X qp σ c'); let hp:= ((hk.ab.lscale factor).unitPay (le_refl (0:ℝ)) (ht 3)).lscale (turnFee q) |>.rscale (highBase G qp σ c'); let hr:= ((hu.ab.rscale (rp q G)).unitPay le_rfl (ht 2)).rscale (Z ((S'.supportExponent+3)*81)); refine (hf.add (hp.add (hx.add (hr.add hh)))).eq_mem ?_
 filter_upwards [price_table G ‹Frost A S' p›] with i hi; unfold totalFee costP costB costM costR preExponent; rw [hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,hi.2.2.2.2.1 (u i), abs_neg,abs_neg]; change _=_; simp only [mul_assoc]
-- Abs Warp payouts
lemma warp_wrap (hp:∀ᶠ i in T,Loft (p i) (n i))(hf:H f δ)(hg:∀ᶠ i in T,|g i| ≤ reward (n i) (p i|>.threshold)*vault (n i) (p i) (f i))(b:ℝ):
 H (fun i=> food G (n i) (p i) (g i)) b ∧ H (fun i=> flare G (n i) (p i) (g i)) b ∧ H (fun i=> (p i|>.threshold)^2 * |g i|) b:= by
 let L i:= Z (((p i).supportExponent+1)*pitch (n i) (p i|>.B));
 have h(k:ℕ): H (fun i=> |(p i).threshold^2*L i*g i*((n i).val:ℝ)^k|) b:=(wrap_hard G hw hp hf hg k b).ab;
 let a:= Z ((S'.supportExponent+1)*81); let C:= (Fintype.card Signed:ℝ); let v:ℝ:= factor* rp q G; have he i: (Fintype.card (Seat (n i)):ℝ)= C*((n i).val:ℝ)^4:= by unfold Seat; rw [Fintype.card_prod, site_card]; push_cast; rfl -- site at averaging?
 let F i:= |(p i).threshold^2* L i*g i*((n i).val:ℝ)^4|; let C':= a*C*v; have hm: ∀ᶠ i in T,flare G (n i) (p i) (g i)=F i*C'∧food G (n i) (p i) (g i)=F i*(C'*turnFee q):= by
    filter_upwards [price_table G ‹Frost A S' p›] with i ht; let Y :ℝ:= pitch (n i) (p i).B; have he':Z (((p i).supportExponent+1)*(Y+81))=L i*a:=by unfold L a; rw [ht.2.2.2.1,mul_add,Real.exp_add]

    unfold food flare F; rw [he,ht.2.2.1, he', ht.2.2.2.2.2 (g i)]; simp only [abs_mul, abs_of_nonneg (sq_nonneg (p i).threshold), abs_of_nonneg (show 0≤ L i from (Real.exp_pos _).le), abs_of_nonneg factor_pos.le, abs_of_nonneg (by positivity : 0≤ ((n i).val:ℝ)^4)]; unfold C' v; generalize rp q G=u; constructor <;> ring
 refine ⟨ ((h 4).rscale (C'*turnFee q)).eq_mem (hm.mono fun i hi=>hi.2.symm), ((h 4).rscale C').eq_mem (hm.mono fun i hi=> hi.1.symm), (h 0).smaller ?_⟩;
 apply Eventually.of_forall; intro i; have he: 1 ≤ L i:=Real.one_le_exp (mul_nonneg (by have ht:= p i|>.exponent_pos; linarith) (Nat.cast_nonneg _)); simp only [pow_zero,mul_one,abs_mul,abs_abs,abs_of_nonneg (zero_le_one.trans he),abs_of_nonneg (sq_nonneg (p i).threshold)]; exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (sq_nonneg (p i).threshold) he) (abs_nonneg _)
end Repair
end YM.AllOrder.Rosary
