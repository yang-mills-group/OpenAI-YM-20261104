import YM.SignedWilsonExpansion.Contrast.Emerald
/-! # Three-energy cancellation extends to post-compensated family (all continuum phases)
    Through BOTH Wilson & MS order coefficients at both shapes. At the end of proof, no
    absolute error assertion at fixed points survives without compact hypothesis.
    Joint tests; post-regulator in independent family too. -/
set_option autoImplicit false
set_option maxHeartbeats 640000
noncomputable section
namespace YM.SignedWilsonExpansion.Carbon.Medi
open FVA2 Register FVA2.Arrival Scale Scale.Jury MS MS.Menus MS.High MS.Local.Physical MS.Native MS.Land MS.Fleet
open MeasureTheory Function Filter Set XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1 Asymptotics PowerSeries Maxwell Maxwell.Free Dframe Reg.Choice
open WickFace ProbeB Contrast
open Belle Belle.Path Belle.Buffet WilsonCoeffUV.Mer.Xa MarqueQ Crops PorchK Future Lesson Dancer Dancer.Drawing Commission
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge}(N:WilsonPrescription G){q: Bool}{Y:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{S:Prescription (Press.portDeck G)}{h:G.Simple}(H: Main.Match N h Y S q)
variable (ν:ℝ) (x:Scale.Stage 3)(p:RealTest 3)(f:Test 3) {b:ℕ}
local notation "W"=> Measure.start N.scheme N.criterion 4
local notation "Z"=> N.scheme
local notation "ψ" => N.criterion
local notation "Q'"=> H.details.toServed.toPosted.toQuoted.toContract.toMission.born
local notation "t0"=> ProbeB.money ( ProbeB.gain Y Z ψ ν )
local notation "K"=> Scale.Measure.outlook N.scheme N.criterion 4
-- exact sample audit after N(r) independent. Harmony.Interpret in MS.
abbrev G4 (N:WilsonPrescription G): Way G 4:= FVA2.Scale.Measure.outlook N.scheme N.criterion 4
abbrev seat (u:Sample 3):= passage ( Speed.forms_t Z ψ u 4 ) -- passage ambiguity
abbrev dol (m:XSpace.Mesh)(i:ℕ)(f:Test 3):ℂ:= Deposit m (fun x=> coeff i ( seat N x )) f
include H
lemma atLens (b:ℕ)(u:Tags G 4 3): Tendsto (fun k=> Speed.forms_t Z ψ k 4 b u) (Gate x.val) (𝓝 ( K 3 x b u )):= by
    simp_rw [ Speed.forms_t, FVA2.Scale.Measure.outlook, FVA2.Scale.Facets.actMark,Dframe.seen ]; exact tendsto_finsetSum _ fun i _=> H.startsInX 4 3 x (i none) ( pulseU i ( Scale.Measure.adjust Z ψ 4 ) u )
lemma forCast : Reg.Choice.Harmony ( Gate x.val ) ( seat N ) ( passage (K 3 x) ):= by
    have he(s: Finset (Fin 3)): Reg.Choice.Harmony ( Gate x.val ) (fun i=> Reg.Point.story ( Speed.forms_t Z ψ i 4 ) (maskE G s) ) ( Reg.Point.story ( K 3 x ) ( maskE G s ) ):= by intro k; simp_rw [Reg.Point.story,coeff_mk]; exact atLens N H x k _
    unfold seat ProbeB.passage Rose.b3; exact Harmony.add (Harmony.sub (he Finset.univ) (Harmony.add (Harmony.add ((he _).mul (he _)) ((he _).mul (he _)) ) ((he _).mul (he _)))) (Harmony.smul (((he _).mul (he _)).mul (he _)) 2)
lemma sings (i:ℕ): Senses (conf 3) (fun x=> coeff i ( seat N x )) (criterion K i):=fun x h'=> by obtain he:= forCast N H ⟨x,h'⟩ i; unfold criterion; simp only [Jury.fxt,dif_pos h']; exact he
lemma fair (i:ℕ): ContinuousOn (criterion K i) (conf 3):=Senses.priced (sings N H i)
lemma limi (i:ℕ): Tendsto (fun m=> dol N m i f) Front (𝓝 ( raw K f i )):= Photo.sees_test _ _ _ (conf_open 3) (sings N H i) (fun _ _ _=>rfl) f.tsupport_subset
lemma limitStory (i:ℕ): Tendsto ( fun m=> dol N m i f - (2:ℂ)^12 * dol N m i (ProbeB.double f) ) Front (𝓝 (quote K f i)):= (limi N H f i).sub ((limi N H _ i).const_mul _)
lemma quoteCost (i:ℕ): quote K f i=f.applyTo (receipt K i):=by
   unfold quote raw receipt; rw [ ProbeB.expands ]; unfold Test.applyTo; simp_rw [ mul_sub ]; rw [integral_sub ( f.smearing ( fair N H i ) ) ?_]; swap; · exact f.smearing ( ( ( fair N H i ).comp (continuous_id.continuousOn.const_smul (2:ℝ)) (fun x hx=> Eq.subst (motive:=fun y=> y∈conf 3) (twice (⟨x,hx⟩:Stage 3)) (Facets.posing (-(Real.log 2)) ⟨x,hx⟩).property) ).const_mul ((2:ℂ)^12 ) )
   congr 1; simp_rw [mul_left_comm (f _) ((2:ℂ)^12),integral_const_mul]
include ν in
lemma changeTicket (j:ℕ)(p:j≤2): quote K f j= quote W f j :=by
    rw [ quoteCost N H, ProbeB.quoted Y Z ψ S h (Q').Taylor (Q').still (Q').base f ν ]; apply Test.apply_eq; intro x hx; let y:Stage 3:=⟨x,hx⟩; change receipt K j y.val=receipt W j y.val; interval_cases j
    · have HE:= AxialBill.freeze Y Z ψ S h (Q').Taylor (Q').still (Q').base y ( Real.log 2 ) ν; rw[ contrast_of,contrast_of,HE.1,HE.2.1 ]
    · have HE:= AxialBill.freeze Y Z ψ S h (Q').Taylor (Q').still (Q').base y ( Real.log 2 ) ν; rw[ contrast_of,contrast_of,HE.2.2.1,HE.2.2.2 ]
    exact (clockE N H ν y f).2.2.2
lemma healthy (ν t:ℝ)(b:ℕ)(m: Tags G 4 3): ContinuousOn (fun x=> mote K b x t m) (conf 3):=by
    apply continuousOn_finsetSum; intro i _; exact (( H.details.toServed.toPosted.toQuoted.toContract.smear ν 4 ).1.light _ _ _).const_mul _
variable {ι:Type}{L:Filter ι}(τ:ι→ℝ)(X:ι→Rose.Badge→Points 3→ℂ) (w:Tendsto τ L (𝓝 0)) (C:∀ᶠ i in L,∀ p: Rose.Badge,ContinuousOn (X i p) (conf 3)) {U:Set (Points 3)}
-- Basket for Open.Post follows on BOTH poses.Any.Permit. reprove bound on ROI.
local notation "ε"=> ( τ ^ b )
omit H
abbrev fans (b:ℕ)(U:Set (Points 3)):Prop:= ∀ p:Rose.Badge, Serves L (fun i y=> X i p y) (fun i y=> mote K b y (τ i) (maskE G p)) U (τ^b)
include H w ν
lemma gains (p:Tags G 4 3)(h:Roi U){b:ℕ} : buys (fun i y=> mote K b y (τ i) p )=O[diners L U](1:ι×Points 3→ℝ):=by
    have hx:(fun v:ι×Points 3=>( (τ v.1):ℂ))=O[diners L U](1:ι×Points 3→ℝ):=isBigO_const_of_tendsto (Complex.continuous_ofReal.continuousAt.tendsto.comp ( w.comp plot_le ) ) one_ne_zero -- infer Rν
    change (fun i=> ∑ j∈_,_)=O[_] _; refine IsBigO.sum fun i _=> (?_);
    obtain hp:= ( H.details.toServed.toPosted.toQuoted.toContract.smear ν 4 ).1; let f(y:Points 3):= Jury.fxt K y i p; have hf: ContinuousOn f (conf 3):= hp.light _ _ _; obtain ⟨C,v⟩:= (h.1.image_of_continuousOn (hf.norm.mono h.2)).bddAbove; have he: buys (fun _:ι=> f)=O[diners L U](1:ι×Points 3→ℝ):= IsBigO.of_bound C ( plot_in.mono fun i h=> (v (mem_image_of_mem _ h)).trans_eq (by simp) ); simpa only [Pi.one_apply,one_mul,mul_one,one_pow] using! ((hx.pow i).mul he)
lemma allowance (k:Roi U)(e:fans (L:=L) N τ X b U)(p:Rose.Badge): Basket (diners L U) b (τ∘Prod.fst) ( ε ∘ Prod.fst ) ( fun i=> Reg.Point.story ( Jury.fxt K i.2 ) ( maskE G p ) ) ( buys (fun i=> X i p) ) :=by
    let v:=maskE G p; let a:=e p; have hz: ε =O[L](1:ι→ℝ):=( ( Wipe.stop w ).pow b|>.congr_right fun i=> one_pow _ )
    refine ⟨fun i _=>?_, Buffet.inCash (banquet.mp a) (gains N H ν τ w v k) (hz.comp_tendsto plot_le),(banquet.mp a).congr_left fun j=>?_⟩; · simp_rw [Reg.Point.story,coeff_mk]; let X'(y:Points 3):= Jury.fxt K y i v; obtain hp:= ( H.details.toServed.toPosted.toQuoted.toContract.smear ν 4 ).1; have HF: ContinuousOn X' (conf 3):=hp.light _ _ _; obtain ⟨C,vC⟩:= (k.1.image_of_continuousOn (HF.norm.mono k.2)).bddAbove; exact Wage.enroll (IsBigO.of_bound C (plot_in.mono fun i hi=> (vC (mem_image_of_mem _ hi)).trans_eq (by simp)))
    change X j.1 p j.2-mote K b j.2 (τ j.1) _=_; rw[timed]; unfold Reg.Point.story Path.mote; simp_rw [coeff_mk]; exact congr_arg (_ - ·) (Finset.sum_congr rfl fun j _=> mul_comm .. )
lemma AllLow (k:Roi U)(e:fans (L:=L) N τ X b U): Serves L (fun i x=>cumul fun j=>X i j x) (fun i x=>calcT (τ i) b (passage ( Jury.fxt K x ))) U ( τ^b ):=by
    have hB:∀ᶠ i:ι×Points 3 in diners L U, |τ i.1|≤1:= plot_le.eventually ( by simpa using (w.norm.eventually_le_const (by simp: ‖(0:ℝ)‖<1)) ); have ht: (fun i=>τ i^(b+1))=o[L] (τ^b):=Wipe.expense w IsEquivalent.refl (Nat.lt_succ_self b); exact banquet.mpr ( (Buffet.scheme ( fun Φ (i:ι×Points 3)=> Reg.Point.story ( Jury.fxt K i.2 ) ( maskE G Φ ) ) (fun Φ i=>X i.1 Φ i.2) (fun _=> allowance N H ν τ X w k e _) hB (ht.comp_tendsto plot_le)).cost )
omit ν w
lemma forecast (t:ℝ)(b:ℕ): ContinuousOn (fun x:Points 3=> calcT t b ( ProbeB.passage ( fxt K x ) )) (conf 3):=by simp_rw [timed]; exact continuousOn_finsetSum _ fun i _=> ( fair N H i ).mul_const _
lemma ledger (t:ℝ)(b:ℕ): f.applyTo (fun y=> calcT t b ( ProbeB.passage ( fxt K y ) ))=∑ i∈Finset.range (b+1),raw K f i * (t:ℂ)^i :=by
    unfold Test.applyTo; simp_rw [timed,Finset.mul_sum,←mul_assoc]; rw [integral_finsetSum ]; · exact Finset.sum_congr rfl fun i _=> (integral_mul_const .. )
    intro i _; exact ( f.smearing ( fair N H _ ) ).mul_const _
include ν in
lemma tale (t:ℝ): f.applyTo (fun y=>calcT t 2 ( ProbeB.passage ( fxt K y ) ))-(2:ℂ)^12*( ProbeB.double f ).applyTo (fun y=> calcT t 2 ( ProbeB.passage ( fxt K y ) ))= quote W f 2*(t:ℂ)^2:=by
    have he:= clockE N H ν podium f; have h0:quote K f 0=0:=(changeTicket N H ν f 0 (by decide)).trans he.1; have h1:quote K f 1=0:=(changeTicket N H ν f 1 (by decide)).trans he.2.1; rw [ ← changeTicket N H ν f 2 (by decide) ]; simp_rw [ ledger N H ]; simp_rw [ Finset.sum_range_succ, Finset.sum_range_zero,zero_add ]; unfold quote at *; rw [ sub_mul ]; rw[show raw K f 0 = _ from sub_eq_zero.mp h0,show raw K f 1=_ from sub_eq_zero.mp h1]; ring
include w ν C
lemma settled {b:ℕ}(e:fans (L:=L) N τ X b (tsupport f)) : (fun i=> aggregate f ( X i )-f.applyTo (fun x=> calcT (τ i) b ( ProbeB.passage ( fxt K x ) )) )=o[L] (τ^b) := paidProfile f (AllLow N H ν τ X w (Testi _) e) ( C.mono fun i hi=> Lark.actual hi ) ( Eventually.of_forall fun _=> forecast N H _ _ )
lemma after (e:fans (L:=L) N τ X 2 (tsupport f))(p:fans (L:=L) N τ X 2 (tsupport (ProbeB.double f))) : (fun i=> aggregate f (X i)-(2:ℂ)^12*aggregate (ProbeB.double f) (X i)- quote W f 2*(τ i:ℂ)^2)=o[L](τ^2):=by
    refine (( settled N H ν f _ _ w C e ).sub ( ( settled N H ν _ _ _ w C p ).const_mul_left ((2:ℂ)^12))).congr_left (fun i=>?_); rw [← tale N H ν f]; ring
end YM.SignedWilsonExpansion.Carbon.Medi
