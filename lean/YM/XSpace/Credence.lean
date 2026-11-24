import YM.XSpace.Bazaar

/-! # Issue Knit meters to remote layouts (shifted relative to local mark) -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Stall
open Sail
open Function Filter Set Lattice Mu Trace MvPolynomial Next.Rank.Normal Contraction Chart2 JetGauge Future Drama Furlough Scale Shade Tide Further.FreeCovariance.KP Playpen
open scoped Topology BigOperators ContDiff
variable {ι Y I : Type} {L:Filter ι} {G:Gauge}{a:ι→ℝ} (h:Tendsto a L (𝓝 0))(S:∀ᶠ i in L,0<a i)
structure Poses (L:Filter ι)(a:ι→ℝ)(F:I→ι→Cover)(x:I→E4) (s:Finset I): Prop where
  payment : ∀ i∈ s,Tendsto (fun t=> actual (a t) (F i t)) L (𝓝 (x i))
  ends : (Set.InjOn x s)

lemma position_pay (p q:Fee G) {v w:ι→Cover}{x y:E4}(he:Tendsto (fun i=> actual (a i) (v i)) L (𝓝 x))(hq:Tendsto (fun i=>actual (a i) (w i)) L (𝓝 y))(hx:x≠y)(h:Tendsto a L (𝓝 0))(S:∀ᶠ i in L,0<a i): Likely L fun i=> (↑(handshake (Calling v a p i) (Calling w a q i)):ℂ) :=by
  let z i:=v i-w i; have hy:Tendsto (fun i=>actual (a i) (z i)) L (𝓝 (x-y)):=by simp_rw [z,actual,Cross.rcast_sub,smul_sub]; exact he.sub hq
  have H:=paid_pair p.due (advertised q.k q.line q.due) (sub_ne_zero.mpr hx) hy S h
  apply Likely.cont (g:= (fun x:ℝ=>(x:ℂ))) _ Complex.continuous_ofReal
  refine ⟨_,H.congr fun i=>?_⟩; unfold Calling handshake; simp_rw [map_smul,LinearMap.smul_apply,smul_eq_mul]; change _*handshake _ _=_ * (_ * handshake _ _ ); -- factor order inspect
  rw [show displace (v i) p.line=displace (w i) (displace (z i) p.line) by rw [displacement, show w i+z i=v i from by unfold z; abel],meter_serves]; rw [show 2+q.k+p.k=p.cost+q.cost by unfold Fee.cost;omega,pow_add]; ring
variable (c:Shade.Cut) (d:ℕ)

def radius (b:ℝ):ℕ:= ⌈c.rOut*3/(2*b)⌉₊
private lemma size (b:ℝ)(h:0<b): c.rOut*3/2≤ b*radius c b ∧ b*radius c b < c.rOut*3/2+b:=by
  have ht:=c.rOut_pos; set R:= c.rOut*3/2; have he : R/b=c.rOut*3/(2*b):=by rw [div_div]
  unfold radius; rw [← he]; have hp:= (div_le_iff₀ h).mp (Nat.le_ceil (R/b)); constructor; · linarith
  have hv: (↑⌈R/b⌉₊:ℝ)-1 < R/b:=sub_lt_iff_lt_add.mpr (by apply Nat.ceil_lt_add_one; unfold R; positivity); have hh:= (lt_div_iff₀ h).mp hv; linarith
include h S
lemma expanding : Tendsto (fun i=> radius c (a i)) L atTop:= by
  refine tendsto_atTop.2 fun m=> ?_; filter_upwards [S,(h.mul_const (m:ℝ)).eventually (ge_mem_nhds (show 0*(m:ℝ)< c.rOut*3/2 by linarith [c.rOut_pos]))] with i hi ht; have he:(m:ℝ)≤radius c (a i):= (mul_le_mul_iff_right₀ hi).1 (ht.trans (size c _ hi).1); exact_mod_cast he
lemma secures : Safety c (fun i=> radius c (a i)) L a:= ⟨c.rOut*3/2,by linarith [c.rOut_pos], S.mono fun i hi=> (size c _ hi).1⟩
variable {x:ι→Cover}{X:E4}
private lemma sized_wall (hz:Tendsto (fun i=> actual (a i) (x i)) L (𝓝 X))(H: 5*c.rOut ≤‖X‖): ∀ᶠ i in L, Clear (c.rOut/8) (radius c (a i)) (a i) (x i):=by
  have hp:= c.rOut_pos
  filter_upwards [S,hz.norm.eventually (le_mem_nhds (show 4*c.rOut< ‖X‖ by linarith)),h.eventually (ge_mem_nhds (show 0<c.rOut/8 by linarith))] with i hi hv hb y hy
  have he:= size c (a i) hi; have ht:= Shade.size_actual hi (x i); have hh: a i*↑(reach y)≤a i*(radius c (a i):ℝ):=by gcongr
  have hx : a i * ↑(reach (x i))≤ a i*((reach (x i+y):ℝ)+reach y):=by 
    have hZ:reach (x i) ≤ reach (x i+y)+reach y:= by rw [← Sail.reach_neg y]; exact le_trans (le_of_eq (by rw [add_neg_cancel_right])) (Sail.tree ..)
    gcongr; exact_mod_cast hZ
  nlinarith [he.2,ht.2]

private lemma peakEye (v:Fee G)(hv:Stops v.line)(hz:Tendsto (fun i=> actual (a i) (-x i)) L (𝓝 X))(H:5*c.rOut ≤ ‖X‖):
    let f i:=bake (Calling x a v i); let g i:=radius c (a i); Studio L a g f ∧ Likely L (fun i=> orchestra d (a i)⁻¹ (gather d (f i))) ∧ Chapter.safety L a c f:=by
  intro f g; have h₀ : 0<c.rOut:= c.rOut_pos; have hx: X≠0:= norm_pos_iff.mp (by linarith); obtain ⟨p,hp⟩:=announcement _ v.due; have he(i): f i= coil v.k v.line (a i) (-x i):= by unfold f Calling coil; rw [map_smul,slid_bake];rfl
  rw [funext he]; refine ⟨hires hp (expanding h S c) S h hv ⟨_,by apply div_pos h₀ (show (0:ℝ)<8 by norm_num),sized_wall h S c hz H⟩, ⟨_, harmonizes (enter hp S h hz hx) (tunes hp hx) h S d⟩,?_,?_⟩
  · refine observes _ (visit X p) 0 (tunes hp hx) (fun l j u=> ranges hp 0 S h hz ?_ (by simpa) l j); simp; simpa using h.smul_const (rcast u)
  intro y hy hy'; refine observes _ (visit X p) y ?_ ?_
  · intro j; exact ((hp j).value _ (show X+y≠0 by intro h; rw [eq_neg_of_add_eq_zero_left h,norm_neg] at H; linarith)).comp _ (contDiffAt_const.add contDiffAt_id)
  intro l j u; refine ranges hp _ S h hz ?_ ?_ _ _; · have ht := marks y h S; simp_rw [Cross.rcast_add,smul_add]; simpa [Playpen.actual] using ht.add (h.smul_const (rcast u))
  intro he; rw [eq_neg_of_add_eq_zero_left he,norm_neg] at H; linarith

-- the real module of transcripts needed by the expectation receiver

def Talent (A:ι→Contact G) := Studio L a (fun i=> radius c (a i)) A ∧ Likely L (fun i=> orchestra d (a i)⁻¹ (gather d (A i))) ∧ Chapter.safety L a c A
omit h S in
private lemma lifeline {T:Type}[NormedAddCommGroup T]{p q:ι→T}(h:Likely L p)(k:Likely L q):Likely L (fun i=>p i+q i):= Likely.add h k
omit h S in
private lemma lifelines {T:Type}[NormedAddCommGroup T][NormedSpace ℝ T]{p:ι→T}(h:Likely L p)(a:ℝ): Likely L (fun i=>a • p i):= Likely.smul (Likely.const L a) h
private lemma oneAdd {A B:ι→Contact G}(X:Talent (L:=L) (a:=a) c d A)(Y:Talent (L:=L) (a:=a) c d B): Talent (L:=L) (a:=a) c d (A+B):=by
  refine ⟨⟨X.1.lives,fun x=> ?_, fun k=>?_⟩,?_,⟨applies X.2.2.1 Y.2.2.1,fun _ h e=>applies (X.2.2.2 _ h e) (Y.2.2.2 _ h e)⟩⟩
  · filter_upwards [X.1.ground x,Y.1.ground x] with i hi hh; simp only [Pi.add_apply,map_add,hi,hh,add_zero]
  · obtain ⟨C,hC,h⟩:=X.1.loans k; obtain ⟨D,hD,d⟩:=Y.1.loans k; refine ⟨C+D,add_nonneg hC hD,?_⟩; filter_upwards [h,d] with i hi dk x hh l e b; simp_rw [Pi.add_apply,map_add, ← Litter.peaked,map_add,Pi.add_apply,Litter.peaked,add_mul]; exact (norm_add_le ..).trans (add_le_add (hi _ hh l e b) (dk _ hh l e b))
  simp_rw [Pi.add_apply,map_add]; exact lifeline (T:=Lows.Hat G d) X.2.1 Y.2.1
local instance ticker (G:Gauge)(d:ℕ): SMul ℝ (Lows.Hat G d):= Module.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
private lemma tint {A:ι→Contact G}(X:Talent (L:=L) (a:=a) c d A)(p:ℝ): Talent (L:=L) (a:=a) c d (p • A):=by
  refine ⟨⟨X.1.lives,fun x=> ?_,fun k=>?_⟩,?_,⟨quieter p X.2.2.1,fun _ h e=>quieter p (X.2.2.2 _ h e)⟩⟩
  · filter_upwards [X.1.ground x] with i hi; simp only [Pi.smul_apply,map_smul,hi,smul_zero]
  · obtain ⟨C,hC,H⟩:= X.1.loans k; refine ⟨‖p‖*C,mul_nonneg (norm_nonneg _) hC,?_⟩; filter_upwards [H] with i hi x hh l e b; simp_rw [Pi.smul_apply,map_smul,← Litter.peaked,map_smul,Pi.smul_apply,Litter.peaked,norm_smul,mul_assoc]; exact mul_le_mul_of_nonneg_left (hi _ hh l e b) (norm_nonneg _)
  simp_rw [Pi.smul_apply,map_smul]; exact lifelines (T:=Lows.Hat G d) X.2.1 p

def interior (h:Tendsto a L (𝓝 0))(S:∀ᶠ i in L,0<a i)(c:Shade.Cut)(d:ℕ): Club G ι where
  carrier := {p|Talent (L:=L) (a:=a) c d p}
  zero_mem':=by
    refine ⟨⟨expanding h S c,fun x=> Filter.Eventually.of_forall fun i=>?_, fun k=>?_⟩,?_, ⟨silence,fun _ _ _=> silence⟩⟩
    · change Scale.press (F:=G.Color) 0 x=0; rw [map_zero];rfl
    · exact ⟨0,le_rfl, Filter.Eventually.of_forall fun i y _ t _ b=>by simp only [Pi.zero_apply,map_zero,← Litter.peaked,norm_zero,zero_mul,le_refl]⟩
    simp_rw [Pi.zero_apply,map_zero]; exact Likely.zero
  add_mem' :=fun X Y=> oneAdd h S c d X Y
  smul_mem' :=fun c' _ X=> tint h S c d X c'
lemma factor {F:I→ι→ Cover}{w:I→E4}{s:Finset I}(X:Poses L a F w s)(H:∀ j∈s, 5*c.rOut ≤ ‖w j‖): Shops a L (interior (G:=G) h S c d) F s:=by
  constructor; · intro i hi j hj hn q p _ _; apply position_pay _ _ (X.payment i hi) (X.payment j hj) (fun p=> hn (X.ends hi hj p)) h S
  intro i hi v hv; apply peakEye h S c d v hv (X:=-w i); · have he:= (X.payment i hi).neg; exact he.congr fun j=>by unfold actual; rw [← smul_neg, ← zero_sub (F i j),Cross.rcast_sub,show rcast 0=0 by ext i; simp [rcast], zero_sub]
  rw [norm_neg]; exact H i hi
end YM.XSpace.Stall
