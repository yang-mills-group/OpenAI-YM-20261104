import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Captains
import YM.Frontier.Tuning.Thick

/-!
# Physical raw vertex expressions before component integrals, continuation ingredients

Contour coordinates here are actual real displacements from the affine mean, not `sqrt β`
times those displacements; later `same_heatContour` gives exactly the original score on the real
slice after integrating with the corresponding Gaussian weights. All tags, hard decisions,
profiles and path contents are evaluated on the SAME real inputs to these prepared formulas.
No holomorphic group/flag extension or displacement of a threshold. This does not price full
normalized path integrals. We study the ordinary vacuum entries; marked work separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier.Tuning.ComplexVertex
open Filter Function Set Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel Bid SliceRows Control Window Census Mask Pulse Itinerary Coat
open Coat Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable (X : Coat T F) (R : Rep G f)

-- `w` is REAL. For held log terms leave `u` separate in the differentiable germ.
-- In actual integration use normalized marginal dimensions of the full support.
def world (w : Air f G) := X.μ + X.atmos w

def heat (β : ℝ) (w : Air f G) := Real.sqrt β • w
lemma restores {β:ℝ} (hb:0<β) (w : Air f G) : X.liftA β (heat β w)=world X w := by
  have he (a:ℝ) (w:Air f G) : X.atmos (a • w) = a • X.atmos w:= by rfl
  unfold liftA heat world gStep;rw [he,smul_smul,inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hb)),one_smul]

/-- Explicit complex normalization *in* compulsory frozen-coordinate terms (Gaussian
marginal normalization and outer token factors are separate). Right half-plane branch. -/
def logMass (Ñ : ChartRatio G) (z:ℂ) := (Real.log Ñ.scale + Fintype.card G.ColorIndex * Real.log (Real.sqrt (2*Real.pi)):ℝ) - (Fintype.card G.ColorIndex : ℂ)/2*Complex.log z
lemma mass_real {Ñ:ChartRatio G} (hÑ:0<Ñ.scale) {β:ℝ} (hβ:0<β) : logMass Ñ β = (Real.log (measure_g Ñ β):ℂ):=by
  have he : measure_g Ñ β=Ñ.scale*(Real.sqrt (2*Real.pi)* (Real.sqrt β)⁻¹)^Fintype.card G.ColorIndex:=rfl
  rw [he, logMass, Real.log_mul hÑ.ne' (pow_ne_zero _ (mul_ne_zero (Real.sqrt_pos.mpr Real.two_pi_pos).ne' (inv_ne_zero (Real.sqrt_pos.mpr hβ).ne'))),Real.log_pow,Real.log_mul (Real.sqrt_pos.mpr Real.two_pi_pos).ne' (inv_ne_zero (Real.sqrt_pos.mpr hβ).ne'),Real.log_inv, Real.log_sqrt hβ.le, ← Complex.ofReal_log hβ.le]
  push_cast; ring

def steamC (Ñ : ChartRatio G) (z : ℂ) (a : ℝ) (A : Stores S)(u : Directions G f) :=
    - z * (X.quoteNear A u + X.far_bills A : ℝ) + (∑ i∈visit A (200*X.B),X.condensation i)+
      (∑ i∈X.plaza (A.dome (304*X.B)), X.gentry Ñ a u i) - (X.pens A).card*logMass Ñ z

def replace (R : Rep G f) (z:ℝ) (E K : ℕ → Config G f → ℝ): Rep G f :=
    { R with beta:=z, activities:= { R.activities with E:=E,K:=K } }
def linearZ (g:ℝ → ℝ)(z:ℂ):= (g 1:ℂ) + (z-1) * ((g 4:ℂ)-g 1)/3

lemma linearZ_of (g:ℝ→ℝ) {a b:ℝ} (h:∀ v:ℝ,0<v→g v=a+v*b) (v : ℝ) (hv:0<v) :linearZ g v=(g v:ℂ) :=by unfold linearZ; rw [h v hv, h (4:ℝ) (by norm_num),h (1:ℝ) (by norm_num)]; push_cast; ring
omit X in
lemma far_affine_expo (i : Raw.LogLetter c f) (x : ℝ) (T : Tube G S) (U : Config G f)(V : Config G c) : ∃ a b:ℝ,∀ β:ℝ,0<β→Raw.expo T x (replace R β 0 0) U V i=a+β*b :=by
  let g v i:=Raw.expo T x (replace R v 0 0) U V i
  change ∃ a b,∀ β:ℝ,0<β→ g β i= _
  by_cases hs : ∀ v:ℝ,0<v→ g v i=g 1 i
  · refine ⟨g 1 i,0,fun v hv=> by rw [hs _ hv,mul_zero,add_zero]⟩
  refine ⟨0,g 1 i,fun v _ =>?_⟩; rw [zero_add]
  rcases i with e|(t|t|t|t|t)
  any_goals exact False.elim (hs (fun _ _=>rfl))
  all_goals simp only [g,Raw.expo,Sum.elim,replace,Raw.translateValue,Raw.pairValue, zero_add] <;> ring
private lemma qlin {β:ℝ} (hβ:0<β) (w : Air f G)(i:Bond f): X.qlinear β (heat β w) i = β*X.qlinear 1 w i := by
  have h j: X.hatted β j= (Real.sqrt β)*(X.hatted 1 j):=by unfold hatted gStep; dsimp only [Pi.smul_apply,Pi.add_apply,smul_eq_mul]; rw [inv_inv,Real.sqrt_one, inv_one,inv_one]; ring
  unfold qlinear heat; dsimp only [PiLp.smul_apply,smul_eq_mul]; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _=>?_ ; rw [h]; calc
    _ = (Real.sqrt β)^2 * (w (i,_) * X.hatted 1 (i,_)) := by ring
    _ = _ := by rw [Real.sq_sqrt hβ.le] -- ring
private lemma qunique' (w : Air f G)(i : Ledger f 2)(β : ℝ): X.qunique (heat β w) i = Real.sqrt β * Real.sqrt β * X.qunique w i:=by
  let t:= Real.sqrt β
  let p:= i.snd.1; let b := (arrive p i.snd.2)
  let K(j k : G.ColorIndex):ℝ:= combo p i.snd.2 (X.finale i.fst) j k
  have hs v: X.qunique v i=(1/2)*(∑ j,(v (p,j))*∑ k,K j k * (v (b,k))) :=rfl
  rw [hs,hs]
  have h j k : K j k * (heat β w) (b,k)=t*(K j k*w (b,k)):= by change K j k*(t*w (b,k))=_; ring
  simp_rw [h,← Finset.mul_sum]
  simp_rw [show ∀ (j : G.ColorIndex) (k:ℝ), (heat β w) (p,j) * (t*k)=(t*t)*(w (p,j)*k) from fun j k=> by change t * w (p,j) * (t*k)= _; ring]
  rw [← Finset.mul_sum]; dsimp only [t]; ring

lemma far_affine (i:LogIndex c f)(a:ℝ)(Ñ:ChartRatio G)(w:Air f G): ∃ m n:ℝ,∀ β:ℝ,0<β→X.farLog (replace R β 0 0) a Ñ (heat β w) i = m+β*n:=by
   let R':= fun v:ℝ=> replace R v 0 0
   change ∃ m n', ∀ β:ℝ,0 < β→ Sum.elim (X.inhale (R' β) a (liftA X β (heat β w))) (Sum.elim (X.Short (liftA X β (heat β w)) Ñ β a) (X.fuel a β (heat β w))) i = _
   rcases i with (t | (t|t|t) | t|t|t|t|t)
   · dsimp only [Sum.elim,inhale]; obtain ⟨m,n,hh⟩:=far_affine_expo R t X.x T (X.input (world X w)) X.V; let p:=X.plaza (space T 0 X.B R t)
     refine ⟨m*X.enforce (2*a) (world X w) p,n*X.enforce (2*a) (world X w) p,fun β hβ=>?_ ⟩
     rw [restores X hβ, show (space T 0 X.B (R' β) t)=space T 0 X.B R t from ?_,hh β hβ]; change _*(X.enforce (2*a) (world X w) p)=_; ring
     rcases t with (_|(_|_|_|_|_)) <;> rfl
   · dsimp only [Sum.elim,Short,speck]
     refine ⟨0,X.speck (world X w) 1 a t,fun β hβ=>?_⟩
     unfold speck; rw [restores X hβ,zero_add]; split_ifs <;> ring
   · dsimp only [Sum.elim,Short]; exact ⟨_,0,fun _ _=>by rw [mul_zero,add_zero]⟩
   · dsimp only [Sum.elim,Short]; exact ⟨X.solo (world X w) Ñ a t,0,fun _ hβ=>by rw [restores X hβ,mul_zero,add_zero]⟩
   · dsimp only [Sum.elim,Coat.fuel]; exact ⟨_,0,fun _ _=>by rw [mul_zero,add_zero]⟩
   · dsimp only [Sum.elim,Coat.fuel]; exact ⟨_,0,fun _ _=>by rw [mul_zero,add_zero]⟩
   · dsimp only [Sum.elim,Coat.fuel]; exact ⟨_,0,fun _ _=>by rw [mul_zero,add_zero]⟩
   · refine ⟨0,X.qfirst 1 w a t,fun β hβ=>?_⟩; dsimp only [Sum.elim,Coat.fuel,qfirst,aperture]; rw [qlin X hβ,restores X hβ,show liftA X 1 w=world X w by simp [liftA, gStep, world], zero_add,mul_left_comm]
   · refine ⟨0,X.chain 1 w a t,fun β hβ=>?_⟩; dsimp only [Sum.elim,Coat.fuel,chain,aperture]; rw [qunique' X, restores X hβ,show liftA X 1 w=world X w by simp [liftA,gStep,world],Real.mul_self_sqrt hβ.le,zero_add,mul_left_comm]

variable {R' : Rep G f}
set_option maxHeartbeats 1000000 in
lemma log_shift (hp:R'.p=R.p)(he:R'.path=R.path)(hc:R'.clip=R.clip)(hr:R'.activities.reg=R.activities.reg) (i:LogIndex c f)(a:ℝ)(Ñ:ChartRatio G)(w:Air f G):
    X.farLog R' a Ñ w i= X.farLog (replace R R'.beta 0 0) a Ñ w i-(Sum.elim (Sum.elim (fun k=>R'.activities.regularOccurrence R'.p k (X.input (X.liftA R'.beta w)) * X.enforce (2*a) (X.liftA R'.beta w) (X.plaza (Raw.space T 0 X.B R (.inl k)))) (fun _=>0)) (fun _=>0) i:ℝ):=by
  rcases i with (_|_|_|_|_|_)|_|_
  · dsimp only [farLog,Sum.elim,inhale,Raw.expo,replace]; rw [show ∀ k:ℕ, Raw.space T 0 X.B R' (.inl k)=Raw.space T 0 X.B R (.inl k) from (by intro i; unfold Raw.space; dsimp; unfold regularFoot; rw [hr])]
    rw [show Activities.regularOccurrence {R.activities with E:=0,K:=0} R.p = 0 from by funext i U; unfold Activities.regularOccurrence masked indicator; split_ifs <;> rfl]
    dsimp only [Pi.zero_apply]; ring
  all_goals dsimp only [replace,farLog,Sum.elim,inhale,Raw.expo,Raw.space]
  all_goals first | exact (sub_zero _).symm | simp only [hc,he,hp,sub_zero]

abbrev Payload (G:Gauge) (f:Side):= ℕ → Config G f → ℂ

def hiddenC (t: ℝ) (s:Support f) (v:Config G f→ℂ) (U:Config G f):= RG.masked t s v U
lemma hiddenC_real {v : Config G f→ℝ} {a : Config G f→ℂ} (h: ∀ y,a y=(v y:ℂ)) (y : Config G f) (t:ℝ) (s:Support f): hiddenC t s a y=Complex.ofReal (RG.masked t s v y):=by unfold hiddenC masked indicator; split_ifs; exact h _; rfl

def Epart (v : Payload G f) (a:ℝ)(w:Air f G) (i:LogIndex c f) := Sum.elim (Sum.elim (fun k=> hiddenC R.p.threshold (R.activities.reg k).support (v k) (X.input (world X w)) * X.enforce (2*a) (world X w) (X.plaza (Raw.space T 0 X.B R (.inl k)))) (fun _=>0)) (fun _=>0) i -- fill underscore

def farLogC (v : Payload G f) (a:ℝ)(Ñ:ChartRatio G)(z:ℂ) (w:Air f G)(i:LogIndex c f) :=
  linearZ (fun β=> X.farLog (replace R β 0 0) a Ñ (heat β w) i) z-Epart X R v a w i

def rawCvertex (v k : Payload G f) (Ñ : ChartRatio G)(z:ℂ) (W a:ℝ)(l:Finset ℕ)(m:ℕ)(w:Air f G)(s:Head S) :=
    let u := world X w
    let U:= X.input u
    s.elim (fun A => if Packets.connected S m X.B A ∧ X.existSeeds A 300 then Complex.exp (steamC X Ñ z a A u)*Contract.order R l (vias S A (300*X.B)) U*tickets A (300*X.B) U X.k*(profiles A X.χ (300*X.B) X.x W U X.k X.V)*X.enforce a u (X.plaza (A.dome (304*X.B))) else 0)
      (Sum.elim (fun p=> k p U * X.enforce (2*a) u (X.plaza (Raw.forcedFoot S.ratio 0 X.B R p))) (Sum.elim (fun i=>Complex.exp (farLogC X R v a Ñ z w i)-1) (fun i=>X.detect u W a R l i)))

structure Aligned : Prop where
  sameP : R'.p=R.p
  path : R'.path=R.path
  clip : R'.clip=R.clip
  reg : R'.activities.reg=R.activities.reg
  forced : R'.activities.forced=R.activities.forced

variable {R}
variable (h:Aligned R (R':=R'))
include h
lemma far_real (v:Payload G f)(he:∀ k y,v k y=(R'.activities.E k y:ℂ))(a:ℝ)(Ñ:ChartRatio G)(w:Air f G)(i:LogIndex c f){β:ℝ}(hβ:R'.beta=β)(hb:0<β): farLogC X R v a Ñ β w i = (X.farLog R' a Ñ (heat β w) i:ℂ):=by
  have hu:=log_shift X R h.sameP h.path h.clip h.reg i a Ñ (heat β w)
  obtain ⟨x,y,hh⟩:=far_affine X R i a Ñ w
  rw [farLogC,linearZ_of _ hh β hb,hu,hβ]
  suffices hv' : Epart X R v a w i= ((Sum.elim (Sum.elim (fun k=>R'.activities.regularOccurrence R'.p k (X.input (X.liftA β (heat β w))) * X.enforce (2*a) (X.liftA β (heat β w)) (X.plaza (Raw.space T 0 X.B R (.inl k)))) (fun _=>0)) (fun _=>0) i:ℝ):ℂ) by rw [hv',Complex.ofReal_sub]
  rcases i with (k|t)|t
  · dsimp only [Epart,Sum.elim,Activities.regularOccurrence]; rw [hiddenC_real (v:=R'.activities.E k) (he k), ←h.reg,← h.sameP, Complex.ofReal_mul, restores X hb]
  all_goals rfl
omit X
private lemma order_eq (l A U): Contract.order R l A U=Contract.order R' l A U:=by unfold Contract.order Contract.charges Contract.covered; simp_rw [h.sameP,h.forced]
include X
private lemma detect_eq (l a u W i): X.detect u W a R l i=X.detect u W a R' l i:= by
  rcases i with (i|i|i|i|i)|i
  any_goals rfl
  dsimp only [detect,Sum.elim,mayor,rawStorm,Contract.charges,Contract.covered]; simp only [h.sameP,h.forced]; congr 15
private lemma steam_real (a Ñ A u){β : ℝ}(hb: R'.beta=β) (hβ:0<β) (hn:0<Ñ.scale): steamC X Ñ β a A u=(X.steamLog R' Ñ a A u:ℂ):=by rw [steamC, mass_real hn hβ,steamLog, hb]; push_cast; rfl

lemma raw_real (v k : Payload G f) (Ñ : ChartRatio G)(W a:ℝ)(l:Finset ℕ)(m:ℕ)(w:Air f G)(s:Head S) {β:ℝ}
   (he:∀ j y,v j y=(R'.activities.E j y:ℂ))(hk:∀ j y,k j y=(R'.activities.K j y:ℂ))(hβ:R'.beta=β)(hb:0<β)(hn:0<Ñ.scale):
   rawCvertex X R v k Ñ β W a l m w s = (X.vertex R' Ñ W a l m (heat β w) s:ℂ) :=by
   rw [vertex,hβ,restores X hb]; rcases s with A|j|j|j
   · dsimp only [Sum.elim,rawCvertex,Pack,steam]; split_ifs with hA hc hA'
     · rw [steam_real X h a Ñ A _ hβ hb hn,order_eq h]; push_cast; rfl
     all_goals first | tauto | rfl
   · dsimp only [Sum.elim,rawCvertex,bag]; unfold Raw.forcedFoot; rw [hk,Complex.ofReal_mul,h.forced]
   · dsimp only [Sum.elim,rawCvertex,raiseAir]; rw [far_real X h v he a Ñ w j hβ hb]; push_cast; rfl
   dsimp only [rawCvertex,Sum.elim]; rw [detect_eq X h]

variable (R)
lemma raw_differentiable (v k : ℂ→Payload G f) (Ñ : ChartRatio G)(z:ℂ) (W a:ℝ)(l:Finset ℕ)(m:ℕ)(w:Air f G)(s:Head S) (he:∀ i y,DifferentiableAt ℂ (fun z=>v z i y) z)(hk:∀ i y, DifferentiableAt ℂ (fun z=>k z i y) z) (hj:z∈Complex.slitPlane): DifferentiableAt ℂ (fun z=>rawCvertex X R (v z) (k z) Ñ z W a l m w s) z:=by
   rcases s with A|i|((i|i)|i)|i
   all_goals dsimp only [rawCvertex,Sum.elim]
   · split_ifs; dsimp only [steamC,logMass]; fun_prop
     exact differentiableAt_const _
   · exact (hk _ _).mul_const _
   · unfold farLogC linearZ Epart; dsimp only [Sum.elim]; unfold hiddenC masked indicator; split
     · have hu:= he i (X.input (world X w)); fun_prop
     fun_prop
   
   all_goals try exact differentiableAt_const _
   all_goals unfold farLogC linearZ Epart <;> dsimp only [Sum.elim] <;> fun_prop

end YM.Frontier.Tuning.ComplexVertex
