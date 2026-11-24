import YM.SignedWilsonExpansion.Chron.Impulse
import YM.SignedWilsonExpansion.Purchase.Imburse
/-! # F6 repeated orders after unit restoration. Keep bound even worst-powered cotangent/coefficient Holland. -/
set_option autoImplicit false
set_option maxHeartbeats 670000
noncomputable section
namespace YM.Integration.Logwood.HeatS
open Function Filter Finset Lattice RG Wilson Asymptotics Real
open Push.GridApprox YM.SignedWilsonExpansion.Commission
open OPE.Therm
open scoped Topology ENNReal BigOperators Classical
open FVA1Physical.Exchange FVA1Physical.Exchange.F6Regular
open YM.SignedWilsonExpansion.Purchases UVClock Schedules
open YM.SignedWilsonExpansion.Purchases.HalfRoof.Minty
open Attach
variable {G:Gauge}{d i r e:ℕ}{H:History G}{ι:Type}
variable {B P A:ι→ℝ} -- missing ι
-- Explicit units only after precision. Capital caps use q(d), lag-weight, and H^pole, product.
abbrev trimS (H: History G) (f N p:ι→ℕ)(S:∀ i,Finset (Edge (Site (H.S.side (f i) (p i))))) := fun i=> ticketA (S i) ((H.rep (N i) (p i) (f i)).p) (H.levels.clock.allowance (f i))
lemma σfund (p:BudgetPoint)(n:Side)(S: Finset (Edge (Site n)))(r:ℝ)(q:0≤r):0≤ ticketA S p r:=by unfold ticketA hitConstant; have hp:0≤∑' i:ℕ,polyExp i:= tsum_nonneg (fun i=> (polyExp_pos i).le); positivity
variable {L:Filter ι}{J:Levels G}
lemma beta_owe (u:Rise B L){A:ι→ℝ}(p:IsEquivalent L A B): Consume B L 1 A:=by
    refine p.isBigO.trans (?_); refine (isBigO_refl B L).congr' (.refl ..) (?_); filter_upwards [u.eventually_gt_atTop 0] with i h; unfold payD Spread; rw [one_mul,exp_log h]
variable (pH:H.Selected) (I:r ≤ d) (u:Rise B L) {N p j:ι→ℕ}(b:Epoch L B H.levels j)(g:∀ᶠ i in L,j i≤ N i)
include pH u b g in
lemma colored (S:∀ i, Finset (Edge (Site (H.S.side (j i) (p i))))) (t:∀ᶠ i in L, ((S i).image Prod.fst).card≤ d) : Wage L (Spread B) (payD B (-1)) (trimS H j N p S):=by
    let F:=H.levels.clock; let K:= F.hatBeta ∘ j; let X:= Spread B; let Y(i):= (( ( halo 8 (( S i ).image Prod.fst) ).card :ℕ):ℝ); let Ω(i):= F.allowance ( j i ); let T (i):=(H.rep ( N i ) (p i) ( j i )).p; let V(i):=((T i).B:ℝ)
    have hw :Maxer L X:= (y_rise u).eventually (eventually_ge_atTop 1)
    have hy:Y =O[L] fun i=> (( d*(8+8+1)^4 :ℕ):ℝ):=by
       apply IsBigO.of_norm_eventuallyLE; filter_upwards [t] with i h; rw [Real.norm_of_nonneg (show 0 ≤ Y i from Nat.cast_nonneg _)]; exact Nat.cast_le.mpr ((Corona.halo_size _ 8).trans (Nat.mul_le_mul_right _ h)) -- conclusion
    have hx : Wage L X 1 V:=by
       have hu : Wage L X 1 (Spread K):= wage_bias (( spread_tie u b ).isBigO); have h': Wage L X 1 (fun i=>Spread K i^2):=  Wage.fix (hu.power 2) (.refl ..) ( by simp; rfl ); refine Wage.rel (Wage.plus hw h' (Wage.unitC (1:ℝ))) ( ?_ ) ; apply IsBigO.of_norm_eventuallyLE; filter_upwards [g] with i he; have hh:(T i).B=Nat.ceil ((Spread K i)^2):=by unfold T; rw [( pH.represents _ _ _ he ).vac]; rfl
       change ‖( (T i).B :ℝ)‖≤ _; rw [Real.norm_of_nonneg (Nat.cast_nonneg (α:=ℝ) (T i).B),hh]; exact (Nat.ceil_lt_add_one (sq_nonneg _)).le
    have he := Wage.plus hw ( (Wage.mul ( Wage.unitC (6:ℝ) ) hx).fix (.refl ..) (by simp)) ( Wage.unitC (2:ℝ) ); have hv := Wage.plus hw ( (Wage.mul he ( Wage.unitC (2:ℝ) )).fix (.refl ..) (by simp) ) ( Wage.unitC (1:ℝ) ); -- failing 1*1 etc
    have hA : Wage L X 1 (fun i=>2*hitConstant ((T i).B)):=by
       unfold hitConstant leg; push_cast; exact Wage.fix (Wage.mul (Wage.unitC _) ( Wage.mul (hv.power 4) (Wage.unitC _) )) (.refl ..) (by simp; rfl)
    have ho : Consume B L (-1) Ω:=by
       have hm:Consume B L (-1/2) (mark K):= ( mark_tie u b ).isBigO.trans (penMap u (EventuallyEq.rfl)) ; have ht:Consume B L (-1) (mark K^2):= by convert ( Consume.power hm (n:=2) ) using 1; norm_num
       refine IsBigO.trans ( ?_: Ω=O[L] (mark K^2) ) ht; apply IsBigO.of_norm_eventuallyLE; have hh:=( Consume.conv u hm (by norm_num: -(1:ℝ)/2 <0)).eventually ( ge_mem_nhds (by norm_num: (0:ℝ)<1)); filter_upwards [hh] with i hi; have hk: 0 < mark K i:= inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans (H.levels.fits.delayed _))); change ‖(mark K i)^((11:ℝ)/5)‖≤ _; rw [ Real.norm_of_nonneg (Real.rpow_nonneg (y:=(11:ℝ)/5) hk.le) ]; exact ( Real.rpow_le_rpow_of_exponent_ge hk hi ( by norm_num: (2:ℝ) ≤ 11/5 ) ).trans_eq ( Real.rpow_two _ )
    have hZ: Wage L X 1 Y:= Wage.rel (Wage.unitC _) hy; have hh:= ( Wage.mul hZ ( Wage.mul hA ( Wage.enroll ho ) ) ); simpa only [one_mul] using hh
variable (S:∀ i, Finset (Edge (Site (H.S.side (j i) (p i))))) (t:∀ᶠ i in L, ((S i).image Prod.fst).card≤ d)
lemma powerP (P:ι→ℝ)(u:Rise B L){T O: ℝ}{E:Type}[NormedAddCommGroup E](z:ι→E)(v:Wage L (Spread B) P z)(h:T < O)(b: Consume B L T P): z=o[L] (payD B O):= Wage.spend ( Wage.transfer v (polyCost u) ) ( spendMark u b h )
lemma stretchP (u:Rise B L){T:ℝ} (k:ℕ) (h: T < k*(-1/2:ℝ)) {V:Type}[NormedAddCommGroup V]{p:ι→V} (v: Wage L (Spread B) (payD B T) p): p=o[L] (( mark B )^k):= Wage.spend ( Wage.transfer v (polyCost u) ) ( mark_power u ( isBigO_refl _ L ) h )
include pH u b g t
lemma rebateS : ∀ᶠ i in L, trimS H j N p S i ≤1/4:=by
   have hx:= powerP _ u _ (colored pH u b g S t) (show (-1:ℝ)<0 by norm_num) ( isBigO_refl _ L )
   have hy : ( trimS H j N p S ) =o[L] (1:ι→ℝ):= hx.congr_right (by rw [payD_zero]; intros; rfl)
   have hm := ( isLittleO_const_iff (l:=L) (f'':=trimS H j N p S) (show (1:ℝ)≠0 from one_ne_zero)).mp hy
   exact hm.eventually (ge_mem_nhds (by norm_num))
variable {T O:ℝ}{M K:ι→ℝ}
lemma endsP (h: T+ ( ↑(e+1:ℕ):ℝ)*(-1:ℝ)<r*(-1/2:ℝ)) (v: Consume B L T M): ( fun i=>16*M i*(trimS H j N p S i)^(e+1))=o[L] ((mark B)^r):=by
   let a:=colored pH u b g S t; let U:= payD B (-1); let b:=a.power ( e+1 ); let c:= Wage.mul ( Wage.mul ( Wage.unitC (16:ℝ) ) (Wage.enroll v)) b; apply stretchP u _ h; apply c.fix (.refl ..) ; rw[payD_add,payD_pow]; simp only [one_mul]; exact EventuallyEq.rfl -- power equality
lemma reserve_ω (v: Consume B L T M): ∀ k :ℕ,∃ e>0,(fun i=> 16*M i* ( trimS H j N p S i )^(e+1) )=o[L] ((mark B)^k):=by
    intro k; obtain ⟨e,h⟩:= exists_nat_gt (T+↑k/2); refine ⟨e+1,Nat.zero_lt_succ _,endsP pH u b g S t (?_) v⟩; push_cast; linarith
end YM.Integration.Logwood.HeatS
