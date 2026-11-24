import YM.SignedWilsonExpansion.Purchase.MomentS
/-! # Exponential tickets in the panel's scale (`payDiag`).
Pre/post oracle talks Wage & κ.X.G. These are per-point clocks compatible with them.
`Eclipse` means period-side looming over *any* inverse power of chosen clock. `declares`
 bounds for actual support panels may be stated first on unfolded epochs.You must use actual φ scales to route.
-/
set_option autoImplicit false
set_option maxHeartbeats 470000
noncomputable section
namespace YM.SignedWilsonExpansion.Purchases.Schedules
open Asymptotics Wilson Gauge RG Push Lattice Source PriceCompiler UVClock WilsonCoeffUV.Bank PathCost
open Set Filter Function Real Next.Rank Perch Commission
open RG.Supply
open scoped Topology Classical BigOperators
variable {G:Gauge} {M:Levels G}{ι κ:Type*}{A U K S Q B ρ:ι→ℝ}{N j k p i m n:ℕ}{L:Filter ι}
variable (h:Rise B L)(b:GentleS M)(g:G.Simple) {v w z:ℝ}
local notation "Y" => Spread B
local notation "ḡ" => mark B
abbrev payD (B:ι→ℝ)(x:ℝ):ι→ℝ:= fun i=> Real.exp ( x*Spread B i )
abbrev Consume (B:ι→ℝ)(L:Filter ι)(x:ℝ)(P:ι→ℝ):= P=O[L] (payD B x)
lemma pay_pos (B:ι→ℝ)(v:ℝ)(i):0<payD B v i:= Real.exp_pos _
lemma payD_add (B:ι→ℝ)(a b:ℝ): payD B (a+b)= payD B a * payD B b:=by ext1 i; rw [payD, add_mul,exp_add]; rfl -- payD expands? rewrite tactic
lemma payD_zero (B:ι→ℝ):payD B 0=1:=by ext1 i; simp only [payD, zero_mul,exp_zero]; rfl
lemma payD_inv (B:ι→ℝ)(a:ℝ):payD B (-a)=(payD B a)⁻¹:=by ext1 i; simp only [payD, neg_mul,exp_neg]; rfl
lemma payD_pow (B:ι→ℝ)(v:ℝ) (n:ℕ):payD B (n*v)=payD B v^n:=by ext1 i; simp only [payD,mul_assoc,Real.exp_nat_mul]; rfl
include h
lemma mark_exp : ḡ =ᶠ[L] payD B (-1/2):=(h.eventually_gt_atTop 0).mono fun i hi=>by change (Real.sqrt (B i))⁻¹= _; rw [ show (Real.sqrt (B i))⁻¹= _ from Paint.logged (B i) hi,payD]; unfold Spread; congr 1; ring
lemma dollar_op (v:ℝ)(p:0<v): ∀ n:ℕ, Tendsto ( dollar B^ n * payD B (-v)) L (𝓝 0) := by
     intro n; let f(i):= v/2*( - (Y i)); have hx:Tendsto f L atBot := (tendsto_neg_atTop_atBot.comp ( y_rise h )).const_mul_atBot (half_pos p); refine squeeze_zero' (Eventually.of_forall fun i=>mul_nonneg (pow_nonneg (hedge 1 _|>.le) _) (pay_pos ..|>.le)) ?_ (Real.tendsto_exp_atBot.comp hx); filter_upwards [ h.eventually (Paint.monitors (n:ℝ) (v/2) (half_pos p)) ] with i hi; change (Perch.bill 1 (B i))^n*_ ≤ _; simp only [Perch.bill,mul_one,payD,←Real.exp_nat_mul, ←Real.exp_add,Function.comp_apply]; apply Real.exp_le_exp.mpr; unfold f Spread; linarith
lemma payD_looms (p:0<v): Rise (payD B v) L:= Real.tendsto_exp_atTop.comp ((y_rise h).const_mul_atTop p)
lemma payD_cuts (p:v<0): Tendsto (payD B v) L (𝓝 0):= Real.tendsto_exp_atBot.comp ((y_rise h).const_mul_atTop_of_neg p) -- method
lemma payD_wage : Wage L (Spread B) (payD B v) (payD B v) := Wage.enroll (isBigO_refl _ L)
lemma payD_fee (p: v ≤ w): payD B v ≤ᶠ[L] payD B w := ((y_rise h).eventually_ge_atTop 0).mono fun i hi=> exp_le_exp.mpr (mul_le_mul_of_nonneg_right p hi)
lemma payD_lt (p:v < w): ∀ᶠ i in L,payD B v i < payD B w i:= (( y_rise h ).eventually_gt_atTop 0).mono fun i hi=> exp_lt_exp.mpr (mul_lt_mul_of_pos_right p hi)
lemma payD_eps (p:v < w): payD B v =o[L] payD B w:= by
    apply (isLittleO_of_tendsto' (Eventually.of_forall (fun i t=> False.elim ((pay_pos B w i).ne' t))) ?_); refine (payD_cuts h (sub_neg.mpr p)).congr (fun i=>?_); rw [payD,sub_mul,exp_sub]
lemma payD_move (p:v≤w)(u:Consume B L v A): Consume B L w A:= u.trans (IsBigO.of_norm_eventuallyLE ((payD_fee h p).mono fun i hi=>by change ‖payD B v i‖≤ _; rw [Real.norm_of_nonneg (pay_pos ..|>.le)]; exact hi)) -- replace
omit h
lemma Consume.ordered (p:∀ᶠ i in L,0≤ A i)(u:A≤ᶠ[L] payD B v): Consume B L v A:=by apply IsBigO.of_bound'; filter_upwards [u,p] with i hi hp; rw [Real.norm_of_nonneg hp]; exact hi.trans (le_abs_self _)
lemma Consume.mul (p:Consume B L v A)(q:Consume B L w U): Consume B L (v+w) (A*U):=by unfold Consume; rw [payD_add]; exact IsBigO.mul p q
lemma Consume.power (p:Consume B L v A): Consume B L (n*v) (A^n):=by unfold Consume; rw [payD_pow]; exact IsBigO.pow p n -- binder n typo
include h
lemma Consume.inc (p:Consume B L v A)(q:v<w): A=o[L] (payD B w):= p.trans_isLittleO (payD_eps h q)
lemma Consume.conv (p: Consume B L v A)(q:v<0): Tendsto A L (𝓝 0):= p.trans_tendsto (payD_cuts h q)
lemma penMap (p:A=ᶠ[L] mark B) : Consume B L (-1/2) A:= (isBigO_refl _ L).congr' ((p.trans (mark_exp h)).symm) (.refl ..)
-- period shell `Eclipse` strong, polynomial ζ schedules still. Eg uses NumSize at epoch l.
structure Eclipse (L:Filter ι)(B P:ι→ℝ):Prop where
     tall (x:ℝ) : payD B x ≤ᶠ[L] P
variable (τ:Eclipse L B U)
include τ
lemma Eclipse.rising : Rise U L:= tendsto_atTop_mono' _ (τ.tall 1) (payD_looms h (zero_lt_one (α:=ℝ)))
lemma Eclipse.power_zone (x:ℝ)(c:ℝ)(p:0<c): Consume B L x (fun i=> U i ^ (-c)):=by
    have H:=τ.tall (-x/c); apply Consume.ordered; · exact H.mono fun i hi=> rpow_nonneg ( (pay_pos .. ).le.trans hi) _
    filter_upwards [H] with i hi; refine (rpow_le_rpow_of_nonpos (pay_pos ..) hi (neg_nonpos.mpr p.le)).trans_eq (?_ : (payD B _ i)^(-c)= _); rw [payD, ← Real.exp_mul]; unfold payD; congr 1; field_simp
lemma Eclipse.by_pred (n:ℕ) : (fun i=> U i ^ n)⁻¹ =ᶠ[L] fun i=> U i ^ (-(n:ℝ)):= ( τ.rising h|>.eventually_gt_atTop 0 ).mono fun i hi=> by dsimp only [Pi.inv_apply]; rw [rpow_neg hi.le,rpow_natCast]
end YM.SignedWilsonExpansion.Purchases.Schedules
