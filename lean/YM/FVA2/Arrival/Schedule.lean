import YangMills.WilsonProof.GraphOperands
import YM.FVA2.Arrival.Top
import YM.XSpace.Aura
/-!
# The common XSpace mesh as a cutoff in LPT/thermal MS

Index over `Sample`; cover anchor picked by integer offset of `center`, so *same positions*
used even at finite regulator. Its inversion margin, half-period, offsets, and all Mesh/Super
conditions verified using `Gate` (see `Runtime`; make the indicated eventual restrictions); no countability condition here nor iteration. The supremum
norm on QP throughout. All centered placement tests in `G.X`. `µ` is log ν, common inverse
measuring length convention retained. Costs in `Runtime.lean`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Arrival.Schedule
open Function Filter Set Finset Metric MeasureTheory Real Lattice
open MS MS.Local.Physical MS.Tide MS.Tide.PeakT MS.Fleet MS.Orbit MS.Vista MS.Vane MS.Tone MS.Rake MS.Land MS.Dial
open XSpace.Cirrus
open scoped Topology ContDiff Classical
variable {n:ℕ} {G:Gauge}
local notation "U"=> Fin n
local notation "Z"=> XSpace.Cirrus.Sample n
variable (i: XSpace.Cirrus.Sample n)
-- geometry independent of any test estimates. Side even.
abbrev psi (m:XSpace.Mesh): Side:= ⟨m.p.side.val/2,by obtain h:= m.p.large; omega⟩
lemma psi_back (m:XSpace.Mesh): periodN (psi m)=m.p.side:= by
 refine PNat.eq ?_; rw [cap_val]; have h:=m.p.even; change 2*( m.p.side.val/2 )=_; omega
def bar (i:XSpace.Cirrus.Sample n): Cover:= fun a=>⌊i.center a / i.F.spacing⌋
def theta (m:XSpace.Mesh) := max (-Real.log m.spacing) 0
lemma theta_value {m:XSpace.Mesh}(h:m.spacing≤1) : theta m= - Real.log m.spacing:= max_eq_left (neg_nonneg.mpr (Real.log_nonpos m.positive.le h))
def σ (i:XSpace.Cirrus.Sample n) (u:U) := i.layout u - bar i
def showR (μ:ℝ) : Trial (XSpace.Cirrus.Sample n) (Fin n) where
    profile:= ⟨fun i=> theta i.F,fun i=> μ-theta i.F,fun _=> le_max_right ..⟩
    side i:= psi i.F
    off u i:= σ i u
    head:= bar
lemma offset (X: Z)(w:U): bar X + σ X w=X.layout w:= by unfold σ; abel
structure Sized (i:XSpace.Cirrus.Sample n): Prop where
    side : 16≤ i.F.p.side.val
    unit : i.F.spacing ≤ 1
    center : welcome i
lemma center_box (h: Sized i)(a:Axis):
    (i.F.p.side.val:ℤ) ≤ 16 * bar i a ∧ 4*bar i a ≤ i.F.p.side.val:= by
 let N:=i.F.p.side.val; let A:= i.F.spacing; let c:=i.center a; let x:= c/A; have hx:=Int.floor_le x; have he:=Int.lt_floor_add_one x; have hp : 0<A:= i.F.positive; obtain hK : 16≤ (N:ℝ):= Nat.cast_le.mpr h.side; have ha : x ≤ ( N:ℝ )/4:= (div_le_iff₀ hp).mpr (( show c≤ A*N/4 from h.center.2 a ).trans_eq (by ring)); have hL : (N:ℝ)/8≤x:= ( le_div_iff₀ hp ).mpr (le_trans (le_of_eq (by ring)) ( show A*N/8 ≤ c from h.center.1 a )); exact_mod_cast (show (N:ℝ) ≤ 16*(bar i a:ℤ) ∧ 4*( (bar i a:ℤ):ℝ )≤ (N:ℝ) from (by change (_:ℝ)≤16*(⌊x⌋:ℤ) ∧ 4*((⌊x⌋:ℤ):ℝ)≤ (N:ℝ); constructor <;> linarith))
local notation "L"=> psi ( XSpace.Cirrus.grab i )
local notation "N"=> periodN L
lemma bar_lift (h:Sized i): Lattice.lift ( wrap (periodN (psi i.F)) (bar i) )=bar i:= by
 rw [psi_back]; refine lift_eq_iff.mpr ⟨ rfl,fun a=>?_⟩; obtain ha:= center_box i h a; obtain hh:=h.side; omega
lemma pdist_bar (h:Sized i): let p:= wrap N (bar i); (periodN L).val ≤ 16*pdist p ∧ 4 * pdist p ≤ (periodN L).val:= by
 intro p; rcases Vista.axis_max p with ⟨j,hj⟩; have ht:= bar_lift i h; have hx:= psi_back (grab i); have H':(periodN L).val=i.F.p.side.val:= congr_arg Subtype.val hx
 constructor
 · let a:Axis:=0; have hP:= Lattice.component_le p a; have hN:=center_box i h a; rw [ show Lattice.lift p=bar i from ht ] at hP; omega
 unfold p at *; rw [hj]; obtain hA:=center_box i h j; change 4* (Lattice.lift (wrap (periodN (psi i.F)) (bar i)) j).natAbs ≤ _; rw [ht]; omega
lemma cleared (h:Sized i)(x:Orbit.Half) : Vista.mine (periodN (psi i.F)) (wrap (periodN (psi i.F)) (bar i)-thin (psi i.F) x):= by
 let y:= wrap N (bar i); unfold Vista.mine; by_cases hx:x=0; · rw [hx,map_zero,sub_zero]; exact (pdist_bar i h).1
 let t:= thin L x; have ht : pdist t = ( L ).val := by rw [show pdist t= ( L ).val*pdist x from Vista.caress ..,bornlf _ hx, Nat.mul_one];
 have he:=cap_val (psi i.F);  obtain hh:= ( pdist_bar i h ).2; change 4*pdist y ≤ _ at hh; change _ ≤ 16*pdist ( y-t ); have hT:pdist t ≤ pdist y + pdist (y-t) := by nth_rw 1 [ show t=y+ -( y-t ) from (by abel)]; exact ( pdist_triangle _ _ ) |>.trans_eq (by rw [pdist_neg]);
 change (periodN (psi i.F)).val ≤ _
 change pdist t=(psi i.F).val at ht; change 4*pdist y ≤ (periodN (psi i.F)).val at hh; omega

-- the placement and scale
lemma bornS {g: XSpace.Mesh}(h:g.spacing≤1) : exp (-theta g)= g.spacing:= by rw [ theta_value h, neg_neg, exp_log g.positive]
lemma track {x:Points n}(h:x∈conf n): Injective (plot x):= Theater.out.injective.comp (show Injective _ from h)
lemma plot_at (w:U)(a:Axis)(p:Points n): plot p w a= p w a:=rfl
lemma plot_exposes : Continuous (plot (n:=n)):= continuous_pi fun i=> Theater.out.toContinuousLinearEquiv.continuous.comp (PiLp.continuous_apply 2 _ i)
def bend : QP:= i.center - i.F.spacing • Tone.embed (bar i)
variable (μ:ℝ)
lemma planes (u:U)(h:i.F.spacing≤1): testP ( showR (n:=n) μ ) i u=plot (familiar i) u + bend i:= by
 change exp (-theta i.F) • embed (σ i u)= _; rw [bornS h]; funext j; rw [Pi.add_apply,plot_at]; change i.F.spacing * embed (i.layout u - bar i) j= i.F.spacing * embed (i.layout u) j - i.center j + (i.center j - i.F.spacing * embed (bar i) j); rw [Tone.emb_sub,Pi.sub_apply]; ring
lemma approaches (w:U)(h:i.F.spacing≤1) : ‖testP ( showR μ ) i w-plot (familiar i) w‖≤ i.F.spacing:= by
 rw [planes i μ w h, add_sub_cancel_left]; apply (pi_norm_le_iff_of_nonneg i.F.positive.le).mpr; intro j; let a:=i.F.spacing; have ha:0<a:=i.F.positive; apply abs_le.mpr; have hx:=Int.floor_le (i.center j / a); have he:=Int.lt_floor_add_one (i.center j / a); rw [le_div_iff₀ ha] at hx; rw [div_lt_iff₀ ha] at he; change -(a:ℝ)≤ i.center j-a*(⌊i.center j/a⌋:ℤ) ∧ i.center j-a*(⌊i.center j/a⌋:ℤ) ≤ _; constructor <;> nlinarith
-- `Gate` and Super estimates (eventually).
variable (z:Points n)
lemma weather : ∀ᶠ i in Gate z,Sized i:= by
 let a:=grab (n:=n); have h:XSpace.Expense.Stretched (Gate z) a:= frontier.wider (liftG z); filter_upwards [h.smaller,( h.horizon ).eventually (eventually_ge_atTop 16), welcomeG z] with i hi hy hz; refine ⟨ Nat.cast_le.mp (?_ : (( 16:ℕ ):ℝ)≤ ( (i.F.p.side.val):ℝ)), hi,hz⟩; exact_mod_cast (show (16:ℝ) ≤ ↑(i.F.p.side.val) from hy)
lemma speed : Tendsto (fun i:Z=> theta i.F) (Gate z) atTop:= by
 let a(i:Z):= XSpace.Cirrus.unit i; have he:Tendsto (fun i:Z=> Real.log (a i)) (Gate z) atBot:= Real.tendsto_log_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨stepG z, Eventually.of_forall fun i:Z=>i.F.positive⟩); exact (tendsto_neg_atBot_atTop.comp he).congr' ((weather z).mono fun i hi=> (theta_value hi.unit).symm )
lemma boom : Tide.Super ( Gate z ) ( showR μ ).side ( showR μ ).profile.θ:= by
 intro a; let m:= grab (n:=n); let k:=⌈a⌉₊; have hk(a:Z):tickA ( showR μ ).side a= XSpace.Expense.sides m a:= by unfold tickA; change ( (periodN (psi a.F)).val:ℝ )=_; rw [psi_back]; rfl
 let T(i:Z):= theta i.F; let q:XSpace.Expense.Stretched (Gate z) m:= frontier.wider (liftG z); filter_upwards [weather z,(q.pay k).eventually_ge_atTop 1] with i hi ht; let y:=i.F.spacing; let p:=tickA ( showR μ ).side i; let h:y= exp (-T i):= (bornS hi.unit).symm; have ht' : 1 ≤ y^k * p:= by rw [← hk i] at ht; exact ht
 change a*T i ≤ log p; apply le_trans (mul_le_mul_of_nonneg_right ( Nat.le_ceil a ) (( showR μ ).profile.room i)); rw [← Real.exp_le_exp,Real.exp_log (δ_p ..)]; rw [h,Real.exp_neg,inv_pow, ← Real.exp_nat_mul] at ht'; obtain H: exp ((k:ℝ)*T i)*1 ≤ p:= (le_inv_mul_iff₀ (by positivity)).mp ht'; rw [mul_one] at H; exact H
lemma lookG : Tendsto (testP ( showR μ )) (Gate z) (𝓝 (plot z)):= by
 apply tendsto_pi_nhds.mpr; intro i; let a:= fun q:Z=> plot ( familiar q ) i; let b:= fun q:Z=> testP ( showR μ ) q i; have h : Tendsto (b-a) (Gate z) (𝓝 0):= tendsto_zero_iff_norm_tendsto_zero.mpr ( squeeze_zero' ( Eventually.of_forall fun _=>norm_nonneg _ ) ((weather z).mono fun v h=> approaches v μ i h.unit) (stepG z)); obtain ht := h.add ( ((( continuous_apply i ).comp plot_exposes ).continuousAt (x:=z)).tendsto.comp (senseG z) ); exact ( show Tendsto b _ _ from (by simpa only [sub_add_cancel, zero_add] using (show Tendsto (b-a+a) (Gate z) (𝓝 (0+plot z i)) from ht)) )
end YM.FVA2.Arrival.Schedule
