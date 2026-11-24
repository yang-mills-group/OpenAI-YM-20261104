import YM.Frontier.Tuning.ClockShift
import YM.Frontier.Tuning.TwoGrades
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Molt
/-! Simultaneous charges in a two-direction complex E/K plane before integrating the
angular head rows. Doesn't divide by any activity, doesn't vary the hard fields used at
evaluation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier.Tuning.TwoMotion
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Blaze Silica Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Clutch Matter PhysicalNext.Repeat.Alabaster PhysicalNext.Repeat.Height Held ClockShift
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R A : Rep G f} {X : Coat T F} {x :Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {z:E}
variable {a C α Z β γ d η ε σ W s b μ r p q v : ℝ} {j n l : ℕ} {Q : ConnectedActivityE6.Target G P}
variable {o : Target.Order G W}
def ticketL (Z p:ℝ)(y y' : LogIndex c f → ℝ)(i:LogIndex c f):= 3*p*(Z^teeth c f i*(y i+y' i))
def ticketK (Z : ℝ)(k h : ℕ→ℝ)(i:ℕ):= Z^2*(k i+h i)
def fans (A r : Rep G f)(Z:ℝ)(e h : Payload G f) : Prop := ∃ μ ν μ' ν' : ℂ, ‖μ‖≤Z ∧ ‖ν‖≤Z ∧ ‖μ'‖≤Z^2 ∧ ‖ν'‖≤Z^2 ∧ e=traitE A r μ ν ∧ h=traitK A r μ' ν'
-- explicit agreement across step-aligned records, not density equality.
lemma shapes (P : Facing R A) (T:Tube G S) (B l:ℕ) : footprints T R l B=footprints T A l B ∧ lengths T R=lengths T A ∧ twigs R T B l=twigs A T B l :=by
  have h : footprints T R l B=footprints T A l B := by unfold footprints roadway; rw [location P,show forcedFoot S.ratio l B R=forcedFoot S.ratio l B A from funext (fun _=>pointed P _ _ _)]
  have hh : lengths T R=lengths T A := by unfold lengths Raw.forcedExtra exCharge Raw.extra Raw.regularExtra; rw [P.params,P.path,P.forced,P.reg]
  exact ⟨h,hh, by unfold twigs; rw [h,hh]⟩
lemma price_shapes (P : Facing R A)(T:Tube G S)(B l : ℕ): roadway T R B l=roadway T A B l ∧ exCharge T R=exCharge T A ∧ Raw.forcedFoot S.ratio l B R= Raw.forcedFoot S.ratio l B A ∧ forcedExtra R=forcedExtra A:=by
    unfold roadway exCharge forcedFoot forcedExtra Raw.space Raw.extra regularFoot regularExtra; rw [P.reg,P.forced,P.path,P.params]; exact ⟨rfl,rfl,rfl,rfl⟩
private lemma spend_add {ι:Type*} {n:Side} {B:ℕ}{a ε:ℝ}{X:ι→Support n}{w v:ι→ℝ}{e:ι→ℕ}{z u:ℝ} (h: Sales B a ε X w e z) (ht:Sales B a ε X v e u): Sales B a ε X (fun i=> w i+v i) e (z+u):=by
  refine ⟨fun j=> by exact add_nonneg (h.nonneg j) (ht.nonneg j), fun x=> ?_⟩
  convert budget_plus (h.hit x) (ht.hit x) using 1
  funext i; by_cases hv:x∈X i <;> simp only [Reserves.tariff,hv,if_pos,if_neg,not_false_eq_true] <;> ring
set_option maxHeartbeats 500000 in
lemma ticket_prices (P':Facing R A){s C U Z S0:ℝ}{k k':ℕ→ℝ}{y y':LogIndex c f→ℝ}{Q : ConnectedActivityE6.Target G P}{o:Target.Order G W}{j:ℕ}{χ:Chi}(hS: StrongEager Q o S0 s Z j v U C χ T R k y)(ht: StrongEager Q o S0 s Z j v U C χ T A k' y')(p : ℝ)(hp:0≤p) (hZ:1≤Z) (hC:6*C≤1):
  (Sales (radiusB S0) Q.relative Q.ε (roadway T R (radiusB S0) Q.halo) (ticketL Z p y y') (exCharge T R) (3*p*(C+C)) ∧
  Sales (radiusB S0) Q.relative Q.ε (Raw.forcedFoot S.ratio Q.halo (radiusB S0) R) (ticketK Z k k') (forcedExtra R) (C+C)) ∧
  ∀ i, Z^teeth c f i*y i+Z^teeth c f i*y' i≤2*C :=by
   have hx :0≤Q.relative:= by unfold Target.relative; linarith only [Q.bound,Q.pos,Q.usable]
   obtain ⟨h,h',hK,hK'⟩:=price_shapes P' T (radiusB S0) Q.halo
   have hu:=ht.logbook; have hm:=ht.along; rw [← h, ← h'] at hu; rw [← hK,← hK'] at hm
   have hh:=hS.logbook; have hs:=hS.along
   refine ⟨⟨?_,?_⟩,fun i=>?H⟩
   case H => exact (add_le_add (hh.atom hx Q.usable.le i (exChart ..)) (hu.atom hx Q.usable.le i (exChart ..))).trans_eq (two_mul _).symm
   · have hw: ∀ i : LogIndex c f, ticketL Z p y y' i = 3*p*(Z^teeth c f i*y i+Z^teeth c f i*y' i):=fun i=>by rw [ticketL,mul_add]
     have he:= spend_add hh hu
     refine he.shift (by positivity) ?_ fun i=> (hw i).le
     exact fun i=> le_of_eq (hw i).symm |>.trans' (mul_nonneg (by positivity) (he.nonneg i))
   convert spend_add hs hm using 1; funext i; unfold ticketK; rw [mul_add]
-- price theorem fits when optional sales in sum across directions; no assumption close in field space
variable {k1 k1':ℕ→ℝ}{k2 k2':LogIndex c f→ℝ}
set_option maxHeartbeats 650000 in
lemma pair_cap (P':Facing R A)(hZ:1≤Z)(ht: StrongEager Q o X.x s Z j v q C X.χ T R k1 k2)(ht': StrongEager Q o X.x s Z j v q C X.χ T A k1' k2') (hC:6*C≤1) {e h:Payload G f} (hF:fans R A Z e h)(p:ℝ)(hp:∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f:E → ℂ)(x:E) (t d:ℝ), Brush j t d f x → t ≤ 1 → Brush j (p*t) d (fun y=>Complex.exp (f y)-1) x)(hp':0≤p) (hs:1 ≤ s){τ:ℂ}(hR:‖τ/R.beta‖ ≤ 3)(k:Finset ℕ) (U:E→ Config G c)(u:E→ Directions G f)(g:E→Air f G)(m:Mode U z j v)(hq:Clutch X x o.a R.beta q z j U u g)(hM:X.manifest)(hK:X.width=o.K):
 let f0 i w:=emberC (vary X (U i)) R (X.input (Vine.worldZ X R.beta x)) (u i) (g i) Q.table o.a W k τ Q.halo e h (.inr w)
 let F0 w:=s * twigs R T X.B Q.halo w
 (∀ i:ℕ,Brush j (ticketK Z k1 k1' i) (F0 (.inl i)) (fun q=>f0 q (.inl i)) z) ∧ ∀ i:LogIndex c f,Brush j (ticketL Z p k2 k2' i) (F0 (.inr (.inl i))) (fun q=>f0 q (.inr (.inl i))) z:=by
 intro f0 F0
 let c_side:= c; let f_side:=f
 rcases hF with ⟨a,b,c,d,hA,hB,hc,hd,rfl,rfl⟩
 obtain ⟨-,hF,htwig⟩:=shapes P' T X.B Q.halo
 obtain ⟨hk,hS⟩:=ht.stamina E F X U u g z x rfl hK rfl hM m hq
 obtain ⟨hk',hS'⟩:=ht'.stamina E F X U u _ z _ rfl hK rfl hM m (clutch_scale X R A x o.a P' hq)
 rw [moving P'] at hk' hS'; rw [← htwig] at hk' hS'
 let I:= X.input (Vine.worldZ X R.beta x)
 let X' i:=(vary X (U i))
 constructor
 · intro i
   have hh:=ComplexBrush.cast_scale c (hS i) |>.gathering (ComplexBrush.cast_scale d (hS' i))
   refine (hh.climb (add_le_add (mul_le_mul_of_nonneg_right hc (hS i).nonneg) (mul_le_mul_of_nonneg_right hd (hS' i).nonneg) |>.trans_eq (Eq.symm (mul_add ..))) le_rfl).shimmy ?H
   exact Filter.Eventually.of_forall fun i'=> Held.mix_K (X' i') R I _ _ _ _ _ _ τ A (fun _ _=>rfl) P' i Q.halo
 intro i
 let S1:=Z^teeth _ _ i*k2 i+Z^teeth _ _ i*k2' i
 have hsmall := (ticket_prices P' ht ht' p hp' hZ hC|>.2 i)
 let f i':= comboLog (X' i') R I (u i') (g i') Q.table o.a τ (traitE R A a b) i
 suffices hh: Brush j (3*S1) _ f z from (hp E f z _ _ hh (by linarith)).climb (by exact le_of_eq (by unfold S1 ticketL; ring)) le_rfl
 by_cases hv : ∃ j:ℕ,i= Sum.inl (.inl j)
 · rcases hv with ⟨j,rfl⟩
   have hv:= hk (.inl (.inl j)); have hv':= hk' (.inl (.inl j))
   have hx:=ComplexBrush.cast_scale a hv |>.gathering (ComplexBrush.cast_scale b hv')
   have he (y:E): f y=a*(logMoment (X' y) o.a R Q.table (u y) I (g y) (.inl (.inl j)))+b*(logMoment (X' y) o.a A Q.table (u y) I (low R A • g y) (.inl (.inl j))) :=(by unfold f; rw [mix_log (X' y) R I (u y) (g y) Q.table o.a τ A (e:=traitE R A a b) (μ:=a) (ν:=b) (fun _ _=>rfl) P' j]; rfl)
   have hh : 0≤S1:= by unfold S1; simp only [teeth,Sum.elim,Raw.extraA,pow_one]; have hZ:=zero_le_one.trans hZ; have hv0:=hv.nonneg; have hv1:=hv'.nonneg; apply add_nonneg (mul_nonneg hZ hv0) (mul_nonneg hZ hv1)
   apply (hx.shimmy (Eventually.of_forall he)).climb ?_ le_rfl
   unfold S1; simp only [teeth,Sum.elim,Raw.extraA,pow_one] at *
   apply (add_le_add (mul_le_mul_of_nonneg_right hA hv.nonneg) (mul_le_mul_of_nonneg_right hB hv'.nonneg)).trans; unfold S1 at hh; simp only [teeth,Sum.elim,Raw.extraA,pow_one] at hh; linarith only [hh]
 let r := if flips c_side f_side i then τ/R.beta else 1
 have hr' : ‖r‖≤3:=by unfold r;split; exact hR; simp
 have he (a:E): f a = r*logMoment (X' a) o.a R Q.table (u a) I (g a) i:= by
   unfold f comboLog;split
   · exfalso; apply hv;exact ⟨_,rfl⟩
   rfl
 apply ((ComplexBrush.cast_scale r (hk i)).shimmy (Eventually.of_forall he)).climb _ le_rfl
 apply mul_le_mul hr' _ (hk i).nonneg (by norm_num)
 unfold S1; exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg (zero_le_one.trans hZ) _) (hk' _|>.nonneg)) |>.trans' (le_mul_of_one_le_left (hk _|>.nonneg) (one_le_pow₀ hZ)) -- syntax
end YM.Frontier.Tuning.TwoMotion
