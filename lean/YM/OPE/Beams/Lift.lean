import YM.OPE.Screens.Lambs
/-! # Cost at tilted normals for a whole film -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Reels
open Function Filter Finset MeasureTheory Lattice RG Wilson Metric Polar
open scoped Classical Topology ContDiff BigOperators
variable {I J L Z:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{f:Filter L}
    {x:L→ (I→ E4)→ J→ E4}{T:L→ℝ}{a b d:ℝ}
    {F H:L→ (I→ E4)→ℂ} {v:I}
set_option quotPrecheck false
local notation "X"=> (I→ E4)
structure Rear (I L: Type) where
    Index : Type
    [fin : Fintype Index]
    x : L→(I→ E4)→ Index→ E4
attribute [instance] Rear.fin
def PriceTilt (R: Rear I L) (i:L) (z:I→ E4) (κ:Ortho) (u:ℝ): Prop:= ∀ j k:R.Index,u*‖R.x i z j-R.x i z k‖ ≤ |time (Ortho.motion κ (R.x i z j))-time (Ortho.motion κ (R.x i z k))|
local notation "G" => Rear I L
structure Lending (I L:Type)[Fintype I][DecidableEq I] (f: Filter L) (T:L→ℝ) (F:L→ (I→ E4)→ ℂ) (q:J→ Rear I L) : Prop where
   bill : ∀ᶠ i in f,∀ z:I→ E4,‖z‖≤1→ DifferentiableAt ℝ (F i) z
   prices (j:J): ∀ᶠ i in f,∀ z:I→ E4,‖z‖ ≤ 1→ Injective ((q j).x i z)
   tilt (Z:Finset Ortho) (u a:ℝ): 0<u → 0<a → ∀ v:I, ∀ᶠ i in f,∀ z:I→ E4, ‖z‖≤ 1→ ∀ k∈Z,(∀ j:J, PriceTilt (q j) i z k u)→ Radiates (F i) z (ray v k) (Real.exp (a*T i^2))
def Lent : Prop := ∃ (J:Type) (_ : Fintype J) (q:J→ Rear I L), Lending I L f T F q -- turn params explicit
variable (ht:Tendsto T f atTop)
def length (I:Type)[Fintype I]:=2*((Fintype.card (I×Axis):ℝ)+1)
lemma length_most : 1 ≤ length I:=by unfold length; linarith only [Nat.cast_nonneg (α:=ℝ) (Fintype.card (I × Axis))]
variable {p:J→ Rear I L}
namespace Lent
variable (h: Lent (f:=f) (T:=T) (F:=F))
include h
lemma copied (j:Axis): ∀ v:I,∀ᶠ i in f,∀ z:I→ E4, ‖z‖≤1→ ∃ K: Ortho, ‖(forwards K).val-basis j‖<knobSize I ∧ Radiates (F i) z (ray v K) (Real.exp (T i^2)) := by
    obtain ⟨A,a,p,hp⟩:=h; intro v; let K(j):=(p j).Index; obtain ⟨Z,t,ht,he,hZ⟩:=chooseTilt K j (knobSize I) knob_pos; filter_upwards [hp.tilt Z t 1 ht one_pos v,eventually_all.mpr (fun i=>hp.prices i)] with i hi hf z hz; obtain ⟨k,hk,hh⟩:= hZ (fun j=>(p j).x i z) (fun j=> hf j z hz); exact ⟨k,he k hk, by simpa only [one_mul] using hi z hz k hk hh⟩
lemma varied (i:I): ∀ᶠ j in f,∀ z∈ closedBall (0:I→ E4) 1,Watches (F j) z (T j^2) (length I):=by
    have he:=eventually_all.mpr (fun a:Axis=>eventually_all.mpr fun v:I=> h.copied a v); obtain ⟨A,fA,p,hp⟩:=h
    filter_upwards [he,hp.bill] with k he ht z hz; have hp := mem_closedBall_zero_iff.mp hz; have he(u a):=he a u z hp; obtain ⟨K,_,hK⟩:= he i timeAxis; exact knobs_cost (F k) _ hK.at_center (ht z hp) he
omit h
private lemma permit {x:X→ℂ}{y:X→ℂ}{z v:X}(hX:Radiates x z v a) (hY:Radiates y z v b): Radiates (fun z=> x z*y z) z v (a*b):=by
    obtain ⟨F,h,e,hF⟩:=hX.holds; obtain ⟨Y,hg,e',hG⟩:=hY.holds; exact ⟨fun z=> F z*Y z,fun z hz=>(h z hz).mul (hg z hz),fun y hy=>by dsimp only; rw [e y hy,e' y hy], fun z hz=>(norm_mul_le ..).trans (mul_le_mul (hF z hz) (hG z hz) (norm_nonneg _) ((norm_nonneg _).trans (hF z hz)))⟩ -- alias use annotation X notation may precedence
include h
lemma realization_arm (G':ℂ→ℂ→ℂ) (g: L→ (I→ E4)→ℂ) (hp: Lent (f:=f) (T:=T) (F:=H)) (hf:∀ᶠ i in f,∀ z:I→ E4,‖z‖ ≤ 1 → DifferentiableAt ℝ (g i) z)
    (he:∀ b:ℝ,0<b→ ∃ c:ℝ,0<c∧ ∀ᶠ i in f,∀ z:I→ E4,∀ v:I→ E4,Radiates (F i) z v (Real.exp (c*T i^2))→ Radiates (H i) z v (Real.exp (c*T i^2)) → Radiates (g i) z v (Real.exp (b*T i^2))) : Lent (f:=f) (T:=T) (F:=g):=by
    obtain ⟨J,hJ,q,hp⟩:=hp; obtain ⟨A,hA,q',hQ⟩:= h; refine ⟨A⊕J, inferInstance, Sum.elim q' q, hf,fun j=>?_ ,fun P u a hu ha v=>?_⟩
    · cases j; exact hQ.prices _; exact hp.prices _
    obtain ⟨b,hb,h⟩:=he a ha; filter_upwards [h,hQ.tilt P u b hu hb v, hp.tilt P u b hu hb v] with i h hx ht z hz k hk hh using h z _ (hx z hz k hk fun j=>hh (Sum.inl j)) (ht z hz k hk fun j=>hh (Sum.inr j))
lemma touch : ∀ᶠ i in f,∀ z:I→ E4, ‖z‖ ≤ 1 → DifferentiableAt ℝ (F i) z := by obtain ⟨_,_,p,hp⟩:=h; exact hp.bill
lemma mul (he: Lent (f:=f) (T:=T) (F:=H)) : Lent (f:=f) (T:=T) (F:=fun i z=>F i z*H i z):= by
    apply h.realization_arm (·*·) _ he ((h.touch.and he.touch).mono fun i hi z hz=> (hi.1 z hz).mul (hi.2 z hz)); intro a ha; refine ⟨a/2,half_pos ha, Eventually.of_forall fun i z v hf hv=>?_⟩; apply (permit hf hv).mono; rw [← Real.exp_add]; exact Real.exp_monotone (by linarith only)
include ht
lemma add (he:Lent (f:=f) (T:=T) (F:=H)) : Lent (f:=f) (T:=T) (F:=fun i z=> F i z+H i z):=by
    apply h.realization_arm (·+·) _ he ((h.touch.and he.touch).mono fun i hi z hz=> (hi.1 z hz).add (hi.2 z hz)); intro a ha; refine ⟨a/2,half_pos ha,?_⟩; filter_upwards [ht.eventually_ge_atTop (2/a),ht.eventually_ge_atTop 1] with i ht hy z v hf hv; apply (hf.add hv).mono; let θ:=a/2*T i^2; have he: 1 ≤ θ:=(by unfold θ; nlinarith only [(div_le_iff₀ ha).mp ht, (le_mul_of_one_le_right (show 0 ≤ T i from zero_le_one.trans hy) hy), mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (show 0 ≤ T i from zero_le_one.trans hy) hy) ha.le]); rw [show a*T i^2=θ+θ from (by unfold θ; ring), Real.exp_add]; nlinarith only [show 2 ≤ Real.exp θ from (le_trans (by linarith only [he]) (Real.add_one_le_exp _))]
-- constant radius cards
omit h
lemma const {x:L→ℂ}(hx:RateLE f T x a): Lent (f:=f) (T:=T) (F:=fun i (_:I→E4) =>x i):=by
    refine ⟨Empty,inferInstance,(fun i=>i.elim), Eventually.of_forall (fun i z _=> differentiableAt_const _),fun i=>i.elim,fun K u b hu hb v=>?_⟩
    filter_upwards [hx (a+1) (by linarith only), ht.eventually_ge_atTop ((a+1)/b), ht.eventually_ge_atTop 0] with i hi hf ht z hz k hk hh using ⟨fun _=>x i,fun _ _=>differentiableAt_const _,fun _ _=>rfl,fun _ _=> hi.trans (Real.exp_monotone (by nlinarith only [mul_le_mul_of_nonneg_right ((div_le_iff₀ hb).mp hf) ht]))⟩
omit [Fintype J] in
lemma sum {s:Finset J}{F':J→ L→ (I→ E4)→ℂ}(h:∀ j∈s,Lent (f:=f) (T:=T) (F:=F' j)) : Lent (f:=f) (T:=T) (F:=fun i z=>∑ j∈s,F' j i z):=by
    induction s using Finset.induction with
    | empty=>simpa using const (I:=I) ht (RateLE.const (0:ℂ) ht)
    | insert j s hj ih=> simpa only [sum_insert hj] using (h j (mem_insert_self ..)).add ht (ih fun i hi=> h i (mem_insert_of_mem hi))
include h
lemma sub (hp:Lent (f:=f) (T:=T) (F:=H)) : Lent (f:=f) (T:=T) (F:=fun i z=> F i z-H i z):=by simpa only [neg_one_mul,sub_eq_add_neg] using! h.add ht ((const ht (RateLE.const (-1:ℂ) ht)).mul hp)
lemma scaled {x:L→ℝ}(hf:RateLE f T x a) : Lent (f:=f) (T:=T) (F:=fun i z=> x i • F i z):=by simp_rw [Complex.real_smul]; apply (const (x:=fun i=>(x i:ℂ)) ht (hf.transfer ?_)).mul h; filter_upwards with i; simp
end Lent
end YM.OPE.Log.Reels
