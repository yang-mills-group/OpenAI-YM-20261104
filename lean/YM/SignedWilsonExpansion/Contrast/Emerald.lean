import YM.SignedWilsonExpansion.Contrast.Carbon
/-! # Tuition for ONE JOINT profile under ONE W assignment. Vaccine for mistaking Jacobian and compensation. -/
set_option autoImplicit false
set_option maxHeartbeats 520000
noncomputable section
namespace YM.SignedWilsonExpansion.Carbon
open FVA2 Register FVA2.Arrival Scale Scale.Jury MS MS.Menus MS.High MS.Local.Physical MS.Native MS.Land MS.Fleet
open MeasureTheory Function Filter Set XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1 Asymptotics PowerSeries Maxwell Maxwell.Free
open WickFace ProbeB Contrast
open Belle Belle.Path Belle.Buffet WilsonCoeffUV.Mer.Xa MarqueQ Crops
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge}(N:WilsonPrescription G){q: Bool}{Y:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{S:Prescription (Press.portDeck G)}{h:G.Simple}(H: Main.Match N h Y S q)
variable (ν:ℝ) (x:Scale.Stage 3)(p:RealTest 3)(f:Test 3) {b:ℕ}
local notation "W"=> Measure.start N.scheme N.criterion 4
local notation "Z"=> N.scheme
local notation "ψ" => N.criterion
local notation "Q'"=> H.details.toServed.toPosted.toQuoted.toContract.toMission.born
local notation "f0" => Rose.coerce p
include H ν
-- nontyped here uses ink.Borrow v. G to recipe
lemma ripe (b:ℕ)(τ:ℝ): ContinuousOn (fun x:Points 3=> calcT τ b ( ProbeB.passage ( fxt W x ) )) (conf 3):=by
    simp_rw [timed]; exact continuousOn_finsetSum _ fun i _=> (pinched Y Z ψ S h (Q').Taylor (Q').still (Q').base ν i).mul_const _
lemma alleges (t:ℝ)(b:ℕ): f.applyTo (fun y=>calcT t b (ProbeB.passage ( fxt W y )))=∑ i∈Finset.range (b+1),raw W f i * (t:ℂ)^i :=by
    unfold Test.applyTo; simp_rw [timed,Finset.mul_sum,←mul_assoc]; rw [integral_finsetSum ]; · exact Finset.sum_congr rfl fun i _=> (integral_mul_const .. )
    intro i _; exact ( f.smearing ( pinched Y Z ψ S h (Q').Taylor (Q').still (Q').base ν _ ) ).mul_const _
lemma plum (t:ℝ): f.applyTo (fun y=> calcT t 2 (ProbeB.passage ( fxt W y ))) - (2:ℂ)^12 * ( ProbeB.double f ).applyTo (fun y=> calcT t 2 (ProbeB.passage ( fxt W y )))= quote W f 2 * (t:ℂ)^2 :=by
     have he:= clockE N H ν podium f; simp_rw [ alleges N H ν ]; simp_rw [ Finset.sum_range_succ, Finset.sum_range_zero,zero_add ] -- conclusion shape
     unfold quote at *; rw [ sub_mul ]; rw[show raw W f 0 = _ from sub_eq_zero.mp he.1,show raw W f 1=_ from sub_eq_zero.mp he.2.1]; ring
omit H ν
variable {ι:Type}{L:Filter ι}(τ:ι→ℝ)(X:ι→Rose.Badge→Points 3→ℂ) (w:Tendsto τ L (𝓝 0)) (C:∀ᶠ i in L,∀ p: Rose.Badge,ContinuousOn (X i p) (conf 3))
abbrev aggregate (f:Test 3)(X:Rose.Badge→ Points 3→ℂ) : ℂ:= f.applyTo fun y=> cumul fun i=> X i y
-- Mask compiler prices partners true-up alongside all positions
abbrev keep (b:ℕ)(f:Test 3):Prop:= ∀ p: Rose.Badge, Serves L (fun i=> X i p) (fun i y=> Path.mote W b y (τ i) (maskE G p)) (tsupport f) (τ^b)
include H w ν C
lemma grape (b:ℕ)(hS:keep (L:=L) N τ X b f) : (fun i:ι=> aggregate f ( X i )- f.applyTo (fun y=> calcT (τ i) b ( ProbeB.passage ( fxt W y ))))=o[L](τ^b):=by
    let V(i:ι):=τ i; have hp: Serves L ( fun i y=> cumul (fun p=> X i p y) ) (fun i y=> calcT (V i) b ( ProbeB.passage ( fxt W y ))) (tsupport f) (τ^b) := Buffet.paysB _ _ H.details.toServed.toPosted.toQuoted h X ( maskE G ) _ ( Path.Testi f ) (( Wipe.stop w ).pow b|>.congr_right fun i=> one_pow _ ) hS w ( Wipe.expense w IsEquivalent.refl (Nat.lt_succ_self b) ); exact paidProfile f hp ( C.mono fun i t=> Lark.actual t ) ( Eventually.of_forall fun i=> ripe N H ν _ _ )
lemma result (A:keep (L:=L) N τ X 2 f)(B:keep (L:=L) N τ X 2 (ProbeB.double f)): (fun i=> ( aggregate f ( X i )- (2:ℂ)^12 * aggregate ( ProbeB.double f ) ( X i ) )- quote W f 2 * (τ i:ℂ)^2 )=o[L] (τ^2):=by
    refine (( grape N H ν _ _ _ w C _ A ).sub ( (grape N H ν _ _ _ w C _ B).const_mul_left ((2:ℂ)^12) )).congr_left (fun i=>?_ ); rw [←plum N H ν f]; ring
lemma collect (A:keep (L:=L) N τ X 2 ( Rose.coerce p ))(B:keep (L:=L) N τ X 2 (ProbeB.double ( Rose.coerce p )))(m:ProbeB.Admire (four N) x p)(s:∀ᶠ i in L,0< τ i): ∀ᶠ i in L,( speakE N p ).re / 2 * ( τ i )^2 ≤ ( aggregate ( Rose.coerce p ) (X i) - (2:ℂ)^12* aggregate ( ProbeB.double ( Rose.coerce p ) ) ( X i ) ).re:=by
   have hx:=result N H ν _ _ _ w C A B; let v:= speakE N p; let U(i:ι):= aggregate (Rose.coerce p) (X i); let V(i:ι):=(2:ℂ)^12*aggregate (ProbeB.double (Rose.coerce p)) (X i); have ht:0<v.re:= ( plank N H ν x p m ).2
   filter_upwards [ s,hx.bound (c:=v.re/2) (by linarith) ] with i hi hw
   let t:=τ i; change ‖( U i - V i ) - v * ( t:ℂ )^2‖ ≤ v.re/2 * ‖t^2‖ at hw; rw [← Complex.ofReal_pow, Real.norm_eq_abs, abs_of_nonneg ( _root_.sq_nonneg t )] at hw; have HA:= Complex.abs_re_le_norm ( ( U i-V i )- v*↑(t^2) ); rw [ Complex.sub_re, Complex.mul_re ] at HA; simp only[Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] at HA; change v.re/2 * t^2≤(U i-V i).re; linarith [ ( abs_le.mp ( le_trans HA hw ) ).1 ]
end YM.SignedWilsonExpansion.Carbon
