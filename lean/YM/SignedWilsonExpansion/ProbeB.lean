import YM.SignedWilsonExpansion.AxialBill
import YM.RG11Proof.Scale.Move
namespace YM.SignedWilsonExpansion.ProbeB
/-! # Smoothed test-wise prediction (one joint test, all 7 normalized moments)

 Make Contrast prior to changing frames, then compare. No operator compensation
 at the changed homes (same W at both); unit/nil arrow odd-order. `Perspective`
 keeps the `Anchor` axis geometry, not choose tests fit to physical extrapolation.
 The interpretation of `Rose.measureₓ` in `Scale.start` is used to remove the
 regulator of the actual independent connected test. -/
set_option autoImplicit false
noncomputable section
open Function Filter Set MeasureTheory Finset Maxwell Maxwell.Free Maxwell.Wick
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus FVA2.Position FVA2.Arrival
open MS MS.Native MS.Local.Physical MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Fleet MS.Theater MS.Land
open Dframe Scale Scale.Facets Scale.Equator Scale.Level Scale.Meter Reg.Token Scale.Jury Reg.Choice
open WickFace PhaseTilt Contrast AxialBill
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {O:Booked (Press.portDeck G)}(M:MS_Data G O)(Y:Initialize G){V:Normalize.Store G}(K: Rose.Pick V)
variable (S:Land.Prescription (Press.portDeck G))(h:G.Simple)(hs:TaylorOKF M (Press.wickInput Y) S)(hr:Favors.Horder S)(hu: Ace.UnitP S)
local notation "K₀" => Measure.start Y K 4
local notation "Ω" => (Finset (Fin 3))
local notation "∆" => AxialBill.contrast
local notation "ρ" => Real.log 2
local notation "φ" => Points 3
local notation "U4" => Way G 4
local notation "π" => Extent.token
local notation "Ξ" => PowerSeries.coeff
local notation "Β" => Sec G 4
local notation "E" => lens G
-- extend arb. value on diagonals: 0 by all-zero moments including full; only off-support irrelevant.
def passage {G:Gauge}(A:ℕ→Point G 4 3) : PowerSeries ℂ:= Rose.b3 (fun s:Finset (Fin 3)=> Reg.Point.story A (maskE G s))
def criterion (F:Way G 4)(n:ℕ)(x:Points 3):ℂ:= Ξ n ( ProbeB.passage ( Scale.Jury.fxt F x ) )
def raw (F:Way G 4) (f:Test 3)(n:ℕ):ℂ:= f.applyTo ( criterion F n )
def double (f:Test 3) := RG11.Scale.compress 3 (-Real.log 2) f
variable (f:Test 3)(p:RealTest 3)
local notation "L" => Rose.coerce p
lemma defined (F:Way G 4)(x:Stage 3)(i:ℕ): criterion F i x.val=Ξ i ( track F x ):= by rw [criterion, exactC ]; rfl
-- independent removal with all priority faces
abbrev testSeat (i:Sample 3):PowerSeries ℂ:= ProbeB.passage ( Rose.measureₓ Y K 4 i )
variable (ν:ℝ)
include ν hs hr hu h
lemma directs : Measure.Aim Y K 4 (Measure.start Y K 4) := by rw [ ← Measure.together Y K ν M S h hs hr hu ]; exact Measure.reaches Y K ν M S h hs hr hu 4
lemma point_cost (x:φ)(hz:x∈conf 3) : Reg.Choice.Harmony ( Gate x ) ( ProbeB.testSeat Y K ) (ProbeB.passage (fxt K₀ x)):= by
   have he (s:Finset (Fin 3)) := ( show Reg.Choice.Harmony (Gate x) (fun i=> Reg.Point.story (Rose.measureₓ Y K 4 i) (maskE G s)) (Reg.Point.story ( fxt K₀ x ) ( maskE G s )) from ( by intro k; simp_rw [Reg.Point.story,PowerSeries.coeff_mk,fxt,dif_pos hz]; exact directs M Y K S h hs hr hu ν 3 ⟨x,hz⟩ k (maskE G s) ) )
   unfold ProbeB.testSeat ProbeB.passage Rose.b3; exact Harmony.add ( Harmony.sub (he Finset.univ) ( Harmony.add ( Harmony.add ( ( he _ ).mul (he _) ) (( he _ ).mul (he _)) ) (( he _ ).mul (he _)) ) ) ( Harmony.smul (( (he _).mul (he _)).mul (he _) ) 2 )
lemma point_senses (i:ℕ): Senses (conf 3) (fun x=> Ξ i (testSeat Y K x)) (criterion K₀ i):= fun x h'=> point_cost M Y K S h hs hr hu ν x h' i
lemma pinched (i:ℕ): ContinuousOn ( criterion K₀ i ) (conf 3):= Senses.priced ( point_senses M Y K S h hs hr hu ν i )
lemma standing (i:ℕ): Tendsto (fun m=> Deposit m (fun x=> Ξ i (testSeat Y K x)) f) Front (𝓝 ( raw K₀ f i )):= Photo.sees_test _ _ _ ( conf_open 3 ) ( point_senses M Y K S h hs hr hu ν i ) (fun _ _ _=>rfl) f.tsupport_subset
-- all real before frame.Id from Store; report positivity later wrapper
local notation "ℜ" => Reg.Unique.CoreR
omit h hs hr hu ν
lemma bronze (s:Finset (Fin 3))(i: Sample 3): ℜ (Reg.Point.story (Rose.measureₓ Y K 4 i) (maskE G s) ):= by
    let u:=maskE G s; have ht: reel 4 ∘ u=u:= by
       funext a; by_cases he:a∈s; · simp only [comp_apply,u,maskE,testE,Rose.missing,if_pos he]; exact Subtype.ext ( Maxwell.Free.realTeam _ _ )
       simp only [comp_apply,u,maskE,Rose.missing,if_neg he]; exact Subtype.ext ( _root_.map_one realForm )
    have hs(k:ℕ): star (Rose.cooked Y V 4 i k u)=Rose.cooked Y V 4 i k u:= by rw [ ← Rose.cookedR, ht ]
    apply Reg.Unique.of_star; intro n; unfold Reg.Point.story; rw [PowerSeries.coeff_mk,Rose.measure_paid ]; change star ( Rose.turn Y K i.F (fun j=> Rose.cooked Y V 4 i j u) n ) = Rose.turn Y K i.F (fun j=> Rose.cooked Y V 4 i j u) n; unfold Rose.turn; simp_rw [ star_sum,star_smul, hs ]; simp
lemma safe (i:Sample 3)(n:ℕ): star ( Ξ n ( ProbeB.testSeat Y K i ) )= Ξ n ( ProbeB.testSeat Y K i ):= by
    apply Reg.Unique.coinR ?_ n; unfold ProbeB.testSeat ProbeB.passage Reg.Unique.CoreR Rose.b3; simp only [two_smul,map_add,map_sub,map_mul]; simp_rw [ show ∀ s:Ω,( (PowerSeries.map (starRingEnd ℂ)) (Reg.Point.story (Rose.measureₓ Y K 4 i) ( maskE G s)))=_ from fun s=> (bronze Y K s i : ℜ _) ]; -- defeq.R
include h hs hr hu ν
lemma hue (z:φ)(hz:z∈conf 3)(i:ℕ): star ( criterion K₀ i z)= criterion K₀ i z:= by
    have he:= ( point_senses M Y K S h hs hr hu ν i ) z hz; exact tendsto_nhds_unique (he.star.congr (fun x=> safe Y K x i)) he
-- contraction audit by Jacobian test motif kept distinct
omit h hs hr hu ν
lemma twice (x:Stage 3): ( posing (-ρ) x).val=(2:ℝ) • x.val:= by simp [Facets.posing,Real.exp_log]
@[simp] lemma measure_t : π (-ρ) 12=(2:ℂ)^12:= by simp [Extent.token,Real.exp_log]
lemma expanded (x:φ): double f x = (( (2:ℂ)^12 )⁻¹)* f ( (2:ℝ)⁻¹ • x ):= by rw [ ProbeB.double, RG11.Scale.compress_apply ]; unfold RG11.Scale.jac RG11.Scale.wide; rw [ RG11.Scale.four_n, Real.exp_neg,Real.exp_log (by norm_num) ]; norm_num
lemma expands (F:φ→ℂ): (ProbeB.double f).applyTo F=f.applyTo (fun x=> F ( (2:ℝ) • x )):= by rw [double,RG11.Scale.reads_compress ]; unfold RG11.Scale.wide; simp [ Real.exp_log ]

def quote (F:Way G 4) (f:Test 3)(i:ℕ) := raw F f i - (2:ℂ)^12 * raw F (double f) i
def receipt (F:Way G 4)(i:ℕ)(x:φ): ℂ:= criterion F i x- (2:ℂ)^12 * criterion F i ( (2:ℝ) • x )
include hs hr hu h ν
lemma receipt_health (i:ℕ): ContinuousOn (receipt K₀ i) (conf 3):= by
    unfold receipt; refine (pinched M Y K S h hs hr hu ν i).sub ( ( show ContinuousOn (fun x:φ=> criterion K₀ i ( (2:ℝ) • x )) (conf 3) from ?_ ).const_mul _ ); exact ( pinched M Y K S h hs hr hu ν i ).comp ( show ContinuousOn (fun p:φ=> (2:ℝ) • p) (conf 3) from continuous_id.continuousOn.const_smul (2:ℝ) ) ( fun x hx=> Eq.subst (motive:=fun y=> y∈conf 3) (twice (⟨x,hx⟩:Stage 3)) ( posing (-ρ) ⟨x,hx⟩ ).property )
omit hs hr hu h ν in
lemma contrast_of (F:U4)(i:ℕ)(x:Stage 3) : receipt F i x.val= AxialBill.contrast F (Real.log 2) x i:= by unfold receipt AxialBill.contrast; rw [measure_t,ProbeB.defined,← twice x, ProbeB.defined]
lemma quoted (n:ℕ): quote K₀ f n=f.applyTo (receipt K₀ n):= by
   unfold quote receipt raw; rw [ expands ]; unfold Test.applyTo; simp_rw [mul_sub]; rw [ integral_sub ( f.smearing (pinched M Y K S h hs hr hu ν n) ) ?_ ]; swap; · apply f.smearing; convert ( pinched M Y K S h hs hr hu ν n ).sub (receipt_health M Y K S h hs hr hu ν n) using 1; funext _; unfold receipt; rw [ Pi.sub_apply ]; abel
   congr 1; simp_rw [mul_left_comm (f _) ((2:ℂ)^12), integral_const_mul]
lemma blackout (q:ℕ)(H:q<2): quote K₀ f q=0:= by
    rw [ quoted M Y K S h hs hr hu f ν q ]; have hv (x:Stage 3): receipt K₀ q x.val=0:= by rw [ contrast_of ]; obtain hi:= AxialBill.freeze M Y K S h hs hr hu x ρ ν; interval_cases q ; exacts [ hi.1, hi.2.2.1 ]
    rw [ Test.apply_eq f ( K:=receipt K₀ q ) ( P:=fun _=> (0:ℂ) ) (fun _ hx=> hv ⟨_,hx⟩ ) ]; simp [Test.applyTo]
lemma removal (n:ℕ): Tendsto (fun m=> Deposit m (fun x=> Ξ n ( ProbeB.testSeat Y K x)) f - (2:ℂ)^12* Deposit m (fun x=> Ξ n ( ProbeB.testSeat Y K x)) (ProbeB.double f) ) Front (𝓝 (quote K₀ f n)):= ( standing M Y K S h hs hr hu f ν n ).sub (( standing M Y K S h hs hr hu _ ν n ).const_mul _ )
local notation "E0" => Ξ 2 ( GroupS.gaugeM Y K M ν (-1) 4 ) E -- parent
-- note duty not just definition as difference! On off-axis profile determined by scale law.presence
abbrev gain (x:Stage 3):ℂ:= Xi G x (( Ξ 2 ( GroupS.gaugeM Y K M ν (-1) 4 ) ) E)
def money (F:Stage 3→ℂ)(x:φ):ℂ:= open Classical in if h:x∈conf 3 then F ⟨x,h⟩ else 0
lemma revenue : quote K₀ f 2=( Real.log 2:ℝ ) • f.applyTo ( ProbeB.money ( gain M Y K ν ) ):= by
    rw [ quoted M Y K S h hs hr hu f ν ]; rw [ Test.apply_eq f ( K:=receipt K₀ 2 ) ( P:=fun p=> ( Real.log 2:ℝ ) • ProbeB.money ( gain M Y K ν ) p ) ?_ ]; swap; · intro x hx; unfold ProbeB.money; simp only [ dif_pos hx ]; exact (contrast_of K₀ 2 (⟨x,hx⟩:Stage 3)).trans ( AxialBill.agree M Y K S h hs hr hu ( ⟨ x,hx ⟩:Stage 3 ) ( Real.log 2 ) ν ).1
    unfold Test.applyTo; simp_rw [ Complex.real_smul, mul_left_comm ( f _ ) (↑(Real.log 2):ℂ), integral_const_mul ]

lemma order0 (x:Stage 3) (hx: WickFace.Holds x) : criterion K₀ 0 x.val= (( (8*Fintype.card G.ColorIndex*pay x 0 1*pay x 0 2*pay x 1 2):ℝ ):ℂ) := by rw [ ProbeB.defined, Contrast.fee0 ( AxialBill.snapshot M Y K S h hs hr hu ν x|>.1 ), Contrast.iris_lens x hx ]; push_cast; ring
lemma at_test (x:Stage 3)(hx:WickFace.Holds x): receipt K₀ 2 x.val=( Real.log 2*G.casimir/(16*Real.pi^2) ) • criterion K₀ 0 x.val := by
    rw [ contrast_of, AxialBill.axial M Y K S h hs hr hu x ρ ν hx, ProbeB.defined, Contrast.fee0 ( AxialBill.snapshot M Y K S h hs hr hu ν x |>.1 ) ]
lemma pos_axis (x:Stage 3)(hx:WickFace.Holds x): 0< ( receipt K₀ 2 x.val ).re:= by
    rw [ at_test M Y K S h hs hr hu ν x hx, order0 M Y K S h hs hr hu ν x hx, Complex.real_smul, ← Complex.ofReal_mul, Complex.ofReal_re ]; have hv:= Gauge.casimir_pos h; have he:0<Fintype.card G.ColorIndex:= Fintype.card_pos_iff.mpr (Landau.Detect.color_ne h); have a:= positive x 0 1 (by decide); have b:= positive x 0 2 (by decide); have c:= positive x 1 2 (by decide); positivity
omit hs hr hu h ν
structure Admire (F:Way G 4) (x:Stage 3) (p:RealTest 3) : Prop where
   axis : WickFace.Holds x
   nonnegative a : 0 ≤ p a
   center : 0<p x.val -- supports include prescribed center
   amount : ∫ x:φ,p x=1
   bound (a:φ): a∈tsupport p→ 0 < ( receipt F 2 a ).re
include hs hr hu h ν
lemma narrows (x:Stage 3)(hx: WickFace.Holds x) (r:ℝ)(hR:0<r): ∃ p:RealTest 3, Admire K₀ x p ∧ tsupport p ⊆ Metric.ball x.val r:= by
    let LL:=receipt K₀ 2; let G':= {z:φ| z∈conf 3∧0<(LL z).re } ∩ Metric.ball x.val r; have hu:G'∈𝓝 x.val := by
       have hp:ContinuousAt (fun z=>(LL z).re) x.val:= Complex.continuous_re.continuousAt.comp ( ( receipt_health M Y K S h hs hr hu ν 2) x.val x.property|>.continuousAt (( conf_open 3).mem_nhds x.property) ); exact Filter.inter_mem ( Filter.inter_mem ( (conf_open 3).mem_nhds x.property ) ( hp.tendsto.eventually ( Ioi_mem_nhds ( pos_axis M Y K S h hs hr hu ν x hx ) ) ) ) ( Metric.ball_mem_nhds _ hR )
    obtain ⟨a,ha,hh⟩:= Metric.nhds_basis_closedBall.mem_iff.mp hu; let φ': ContDiffBump x.val:= ⟨ a/2,a,by linarith,by linarith ⟩; let f':= φ'.normed ( ( volume : Measure φ) ); let p:RealTest 3:=⟨ f',φ'.contDiff_normed,φ'.hasCompactSupport_normed,fun x hx=> ( hh ( φ'.tsupport_normed_eq (μ:=volume) ▸ hx ) ).1.1 ⟩; refine ⟨ p,⟨ hx, fun p=> φ'.nonneg_normed p, ?_,φ'.integral_normed, fun p hp=> ( hh (show p∈ Metric.closedBall x.val a from φ'.tsupport_normed_eq (μ:=volume) ▸ hp) ).1.2 ⟩, fun y h=>( hh (show y∈ Metric.closedBall x.val a from φ'.tsupport_normed_eq (μ:=volume) ▸ h) ).2 ⟩; change 0<f' x.val; unfold f' ContDiffBump.normed; rw [ φ'.one_of_mem_closedBall (( Metric.mem_closedBall_self φ'.rIn_pos.le )) ]; exact div_pos zero_lt_one φ'.integral_pos
lemma price_pos (x:Stage 3)(hp: Admire K₀ x p): 0< ( quote K₀ (Rose.coerce p) 2 ).re:= by
    rw [ quoted M Y K S h hs hr hu (Rose.coerce p) ν 2 ]; unfold Test.applyTo; let g(z):= ( receipt K₀ 2 z ).re; let HH:= (Rose.coerce p).smearing ( receipt_health M Y K S h hs hr hu ν 2 ); rw [ show (∫ x:φ,(Rose.coerce p) x*receipt K₀ 2 x).re=∫ x:φ,((Rose.coerce p) x*receipt K₀ 2 x).re from (integral_re HH).symm ]; let f(x:φ):=(p x*g x); have he(x:φ) : ( (Rose.coerce p x) * receipt K₀ 2 x ).re= f x:= by unfold f g; change (( (p x:ℝ):ℂ ) *_).re=_; simp
    simp_rw [ he ]; have hf(x:φ)(hx:p x≠0): 0<f x:= mul_pos ( lt_of_le_of_ne ( hp.nonnegative _ ) (Ne.symm hx) ) ( hp.bound x ( subset_closure hx ) );
    have hz: Integrable f:= by obtain ht:= HH.re; change Integrable (fun x:φ=> (( Rose.coerce p x ) * receipt K₀ 2 x ).re ) at ht; simp_rw [he] at ht; exact ht
    refine ( integral_pos_iff_support_of_nonneg (f:=f) ?_ hz ).mpr ?_; · intro x; by_cases hx:p x=0; unfold f; rw [hx,zero_mul]; exact le_rfl; exact (hf x hx).le
    have ht: 0<( volume ( Function.support p ) ):=( isOpen_ne_fun p.continuous continuous_const ).measure_pos volume (⟨ _, (hp.center).ne' ⟩);
    exact lt_of_lt_of_le ht (measure_mono fun x hx=> (hf x hx).ne')
lemma billed_real : star ( quote K₀ L 2 )= quote K₀ L 2:= by
    rw [ quoted M Y K S h hs hr hu (Rose.coerce p) ν 2 ]; unfold Test.applyTo; rw [  show star ( ∫ x:φ,(Rose.coerce p) x*receipt K₀ 2 x )= ∫ x:φ,star ((Rose.coerce p) x * receipt K₀ 2 x ) from integral_conj.symm ]; refine integral_congr_ae ( Eventually.of_forall fun x=>?_ ); by_cases hx:x∈conf 3; swap; · have he:= Test.vanishes (Rose.coerce p) hx; simp [he]
    have hh:= hue M Y K S h hs hr hu ν; unfold receipt; simp_rw [ star_mul',star_sub,hh x hx, star_mul', hh _ ( Eq.subst (motive:=fun z=> z∈conf 3) ( twice ( ⟨ x,hx ⟩:Stage 3 ) ) ( posing (-ρ) (⟨x,hx⟩: Stage 3)).property ),star_pow]; change _=_; simp [Rose.coerce]
end
end YM.SignedWilsonExpansion.ProbeB
