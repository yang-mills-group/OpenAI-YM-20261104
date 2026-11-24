import YM.MS.ScaleForest.Reinstate
import YM.MS.ScaleForest.Quotients
/-!
# Actual single-pin and bulk forest amplitudes: a common analyticity disk at all lengths

Mass and engineering weights exactly as used in computing pole polynomials.
Decouple physical mass/tensor shift using stars. `Rent X n` is a uniform
Laurent lower bound on all explicit-loop pages at the nominal scale. Prove
norm bounds for compensated/paid symbols by calculating co-moving bill.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect Tone Momentum Osc Fiddle Metric
open scoped Topology ContDiff
variable {G : Gauge} {I J : Type} [TopologicalSpace I] {X : Curtain G I} {R T a b : ℝ} {p : ℤ} {n k h : ℕ}

-- w=0, bulk or unit. Signed weight uses s (retained length).
abbrev gradeMass (μ:ℝ)(w k:ℕ) (z:ℂ)(s:ℝ):= Pearl.weight z k (μ+s)*amount (-(w:ℂ)) s

def slicePage (μ:ℝ)(w k:ℕ) (f:Coat G) : Curtain G I := fun z s _=> gradeMass μ w k z s • f z
def startPaid (μ:ℝ)(w:ℕ)(F:Flats G) : Curtain G I:= ∑ i∈F.support, slicePage μ w i (F i)

-- scales out to the actual ONE-region input. Atlas not needed since F arbitrary all scales; z can be junk.
omit [TopologicalSpace I] in
theorem starter (F:Flats G) (μ:ℝ) (w h:ℕ) (z:ℂ)(s:ℝ) (x:I) : backing ((w:ℂ)-h) (startPaid μ w F) z s x=Parade F h μ s z := by
   unfold backing Parade; simp_rw [startPaid,Finset.sum_apply,← cert,map_sum,Finsupp.sum, ew];
   refine Finset.sum_congr rfl fun i _=>?_;
   unfold slicePage gradeMass; rw [mul_smul,map_smul (plower ..),map_smul (plower ..),cert, ← Alps.shift]; ring_nf

-- same palette input can be sent at all test parameters. `paidCurve` with bookkeeping independent.
def Sized (u b:ℝ)(n:ℕ)(p:ℤ)(F:Curtain G I): Prop:= ∃ R, Enough R∧∃Y:Curtain G I,Iris (taper n F) Y ∧ Waves R p Y∧Envelope R u b Y
omit [TopologicalSpace I] in
private theorem paint (F:Curtain G I) (w:ℕ) : Iris (taper w F) (taper w F):= EventuallyEq.rfl

def Kit (u:ℝ)(p:ℤ) (F:Curtain G I): Prop:= ∀ ε:ℝ, 0<ε→∃R, Enough R∧Waves R p F∧Envelope R (-u - ε) (u-ε) F

section
variable (k n w:ℕ)(μ:ℝ) {f: Coat G}
private theorem gradeTape {z:J→disc R}{s:J→ℝ}{ε:ℝ} (hR : 2*R*k ≤ ε) : scaleC 0
    (fun i=> levy (-(w:ℝ)-ε) ((w:ℝ)-ε) (s i)) (fun i=> ‖gradeMass μ w k (z i) (s i)‖) := by
   let D:=exp (2*k*|μ| *R); refine ⟨D,(by unfold D; positivity),0,fun i p hp=>?_⟩; let a:= (z i).val; obtain hv:= abs_le.mp ((Complex.abs_re_le_norm a).trans (mem_ball_zero_iff.mp (z i).property).le ); dsimp only; rw [ pow_zero,mul_one,gradeMass,norm_mul,Mell.amount_norm,Pearl.cubic,Complex.norm_exp]; unfold D
   simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re,Complex.neg_re,Complex.mul_re,gNat,zero_mul,sub_zero]; change exp ((μ+s i)*(-2*k)*a.re) * _ ≤ _
   have hc : -2*k*μ*a.re ≤ 2*k*|μ| *R := by
      have h : -(μ*a.re) ≤ |μ| *R:= by refine ( neg_le_abs _ ).trans ?_; rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_le.mpr hv) (abs_nonneg _)
      rw [ mul_assoc _ _ R ]; nlinarith [Nat.cast_nonneg (α:=ℝ) k]
   rcases le_total (s i) 0 with h|h <;> [rw [ulev _ _ h]; rw [ilev _ _ h]] <;> rw [ ← Real.exp_add, ← Real.exp_add ] <;> apply exp_monotone
   · have he : 2*(k:ℝ)*a.re ≤ ε:= by nlinarith [hv.2, Nat.cast_nonneg (α:=ℝ) k]
     nlinarith [mul_le_mul_of_nonpos_right he h]
   have he : -(2*k)*a.re ≤ ε:= by nlinarith [hv.1,Nat.cast_nonneg (α:=ℝ) k];
   nlinarith [mul_le_mul_of_nonneg_right he h]

private theorem pageFit (hx : altitude n f)(hp : To f (sturdy false G))(hr : To f (good p G)) : ∃g:Coat G,paid n f=ᶠ[dotty] g ∧∃ R,Enough R∧ Hol (disc R) g∧∃ S:ℝ, Enough S ∧ S < R∧∀ z∈disc S,Sturdy false (g z)∧Goods p (g z):= by
   obtain ⟨x,V,R,hR,hV,hP,rfl⟩:= hx; let T:=min R (1/4); let W:=lt_min hR Enough.simple.1; have he:∀ᶠ z in dotty, Sturdy false (V z) ∧ Goods p (V z):= by
     filter_upwards [hp,hr,hP] with z hp hr hv; rw [hv]; exact ⟨ (sturdy ..).smul_mem (z^n) hp,(good ..).smul_mem (z^n) hr⟩
   obtain ⟨r,hr,h_S⟩:= dotty_mem.mp he; let S:= min r (T/2); refine ⟨ V,hP.symm,T,⟨ W,min_le_right .. ⟩,hV.mono (Metric.ball_subset_ball (min_le_left ..)), S,enough_le (R:=T) ⟨ W,min_le_right .. ⟩ (lt_min hr (half_pos W))
     ((min_le_right ..).trans (half_le_self W.le)), lt_of_le_of_lt (min_le_right ..) (half_lt_self W),fun z hz=>?_⟩
   rcases eq_or_ne z 0 with rfl|hz'
   · have hm:= Shine.Wind.cake hV hR; exact ⟨ Shine.Wind.time hm (Eventually.mono he (fun _ h=> h.1 )), Shine.Wind.peerG hm (Eventually.mono he (fun _ h=> h.2))⟩
   exact h_S _ (ball_subset_ball (min_le_left ..) hz) hz'

private theorem singleSized (hx : altitude n f)(hp : To f (sturdy false G))(hr : To f (good p G)) (b : ℝ) (hb:0<b): Sized (I:=I) (-(w:ℝ)-b) ((w:ℝ)-b) n p (slicePage μ w k f):= by
   obtain ⟨g,hg,R,hR,hV,T,hT,hU,hg'⟩:= pageFit n hx hp hr; let S:=min T (b/(2*k+2)); have he: S ≤ T:= min_le_left ..; have hm : S<R:= lt_of_le_of_lt he hU; let H:= enough_le hT (lt_min hT.1 (by positivity : 0<b/((2:ℝ)*k+2))) he;
   let V:Curtain G I:= slicePage μ w k g
   refine ⟨ S,H,V, hg.mono (fun z hz=>?_ ),⟨ ?_, fun s _=> ?_,fun z hz s x=> ?_,fun z hz s x=> ?_ ⟩, fun J z s v=>?_ ⟩
   · funext s x; change z^n • gradeMass μ w k z s • f z=gradeMass μ w k z s • g z; rw [← hz]; exact smul_comm ..
   · intro m l; let X(i:Atlas I S):ℂ:= i.1; have hh: Continuous X:= continuous_subtype_val.comp continuous_fst;
     have hs: Continuous (fun i:Atlas I S=> gradeMass μ w k (X i) (τtest i)):= by unfold gradeMass τtest amount; simp_rw [cubic]; fun_prop
     refine hs.mul (show Continuous (fun i:Atlas I S=>g (X i) m l) from continuous_iff_continuousAt.mpr fun i=>?_); exact (hV.top _ _ _ ( ball_subset_ball hm.le i.1.property)).continuousAt.comp (f:=X) (hh.continuousAt (x:=i))
   · exact (hV.mono (ball_subset_ball hm.le)).rate (x:= fun z:ℂ=> gradeMass μ w k z s) (fun i _=> by simp_rw [gradeMass,cubic]; fun_prop)
   · exact Sturdy_scale (hg' _ (ball_subset_ball he hz)).1 _
   · exact (good p G).smul_mem (gradeMass μ w k z s) (hg' _ (ball_subset_ball he hz)).2
   have hv : 2*S*k ≤ b := by have hx:= (le_div_iff₀ (show 0< (2:ℝ)*k+2 by positivity)).mp (show S ≤ b/(2*k+2) from min_le_right ..); have hs:0<S:=H.1; nlinarith
   have hF : fell 0 1 (fun i:J=>g (z i)):= price_shift (hV.price 0 S H.1 (Metric.closedBall_subset_ball hm)) (fun i:J=> (⟨ (z i).val,ball_subset_closedBall (z i).property⟩:closedBall (0:ℂ) S));
   unfold OnTest V slicePage; convert! fall_scale hF (gradeTape (z:=z) (s:=s) k w μ hv) using 1; ext; simp
end

lemma Sized.plus (h : Sized a b n p X) {Y:Curtain G I} (he : Sized a b n p Y) : Sized a b n p (X+Y) := by
   obtain ⟨R,hR,F,h,hX,hF⟩:= h; obtain ⟨T,hT,U,ht,hU,hY⟩:= he;
   refine ⟨ min R T,hR.pair hT,F+U,?_ ,(hX.shrink (min_le_left ..)).plus (hU.shrink (min_le_right ..)), (hF.shrink (min_le_left ..)).add (hY.shrink (min_le_right ..))⟩
   exact (show taper n (X+Y)=taper n X+taper n Y from funext (fun z=> smul_add ..)) ▸ (EventuallyEq.add h ht)
lemma Sized.zero (a b:ℝ)(n:ℕ)(p:ℤ): Sized a b n p (0:Curtain G I):= by
   refine ⟨ _,Enough.simple,0,?_,Waves.zero ..,Envelope.zero _ _ _ ⟩; exact Eventually.of_forall fun i=> smul_zero ..
lemma Sized.finitePlan {F:J→Curtain G I} (s:Finset J) (h:∀ i∈s, Sized a b n p (F i)) : Sized a b n p (∑ i∈s,F i) := by classical induction s using Finset.induction with| empty=> simpa using Sized.zero a b n p| insert i s hi ih=> rw [Finset.sum_insert hi]; exact (h i (by simp)).plus (ih (fun i hi=>h i (Finset.mem_insert_of_mem hi)))
lemma Sized.live (h:Sized a b n p X) : Gazed (taper n X) := by
   obtain ⟨R,hR,Y,ht,hV,hP⟩:= h; intro t x
   exact ⟨_,Lift.congr (Lift.trim (hV.hol t x) hR.1) (Eventually.mono ht (fun i hi=> Eq.symm (congr_fun (congr_fun hi t) x)))⟩

variable (t h:ℕ) {F:Flats G} (μ:ℝ)

theorem sizedPlan {g:Bool} (he:Moony g F)(ht : OfRank p F)(hp:Rent F n) (b:ℝ)(hb:0<b) :
    Sized (I:=I) (-(t:ℝ)-b) ((t:ℝ)-b) n p (startPaid μ t F) :=
   Sized.finitePlan F.support (fun i _=> singleSized i n t μ (hp i) ((all0 he i).dice) (ht i) b hb)

-- single hol estimates prior to gluing. Kit cost for compensated meromorphic curve
-- (also for yet unpaid if already live). Atlas independent.
theorem Sized.population (hp:Gazed X)(hx:Sized a b n p X): ∃ R, Enough R ∧ Waves R p (populated X) ∧ Envelope R a b (populated X) := by obtain ⟨R,hR,Y,hY,hh,hT⟩:= hx; exact reduceLift hR hh hT hY hp
lemma compensated {g:Bool} (he:Moony g F)(ht: OfRank p F)(hx: Rent F n): Kit (I:=I) (t:ℝ) p (populated (taper n (startPaid μ t F))) := by
   intro b hb; obtain hm := sizedPlan (I:=I) t μ he ht hx b hb
   apply Sized.population hm.live (n:=0) ?_; obtain ⟨R,hR,V,h,hP,hQ⟩:=hm; refine ⟨ R,hR,V,?_,hP,hQ ⟩; exact (Eventually.mono h (fun z hz=> by rw [taper,pow_zero,one_smul]; exact hz))
omit [TopologicalSpace I] in
lemma start_live (hp: Stay h F): Gazed (I:=I) (startPaid μ t F):= by
   intro s x; obtain ⟨u, hu⟩:= hp μ s; refine ⟨ _,Lift.congr (Lift.plowX hu (-s) ((t:ℂ)-h)) ?_⟩;
   refine Eventually.of_forall fun i=>?_;
   dsimp only; rw [ ← starter F μ t h i s x ]; unfold backing; rw [snow,neg_add_cancel,posing]
lemma compensated_free {g:Bool} (he:Moony g F)(ht: OfRank p F)(hx : Stay h F): Kit (I:=I) (t:ℝ) p (populated (startPaid μ t F)) := fun b hb=> (sizedPlan t μ he ht (sufficientBound (Moony.toast he)) b hb).population (start_live t h μ hx)

def asLeaf (F:Flats G)(μ:ℝ)(t:ℕ) : Curtain G I:= populated (startPaid μ t F)
omit [TopologicalSpace I] in
lemma leafValue (F: Flats G) (hv: Stay h F) (s:ℝ) (x:I) : backing ((t:ℂ)-h) (asLeaf F μ t) 0 s x = ruby (Parade F h μ s) 0:= by
   unfold asLeaf backing; rw [popAt]; refine (chosen (n:=0) ?_); -- 0
   exact Lift.congr (Lift.plowX (Rub (start_live t h μ hv s x) 0) s ((t:ℂ)-h)) (Eventually.of_forall fun z=> starter ..)
end YM.MS.ScaleForest
