import YM.FormalBulk08.Plait.Oaths

/-! Deck with active y on-axis, stationary compatibility hypothesis is
uncentered F. η-translation carries 2-sided local determinant *at all
chart points*, no off-shell tensor-price estimate. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Plait
open Wick Series Orb Jets Filter Function
open scoped BigOperators Matrix Topology Classical ContDiff
variable {V I:Type*}[Fintype V][Fintype I]

def secondL (x:Jets.Rays (V⊕I)):= x ∘ Sum.inr
def firstL (x:Jets.Rays (V⊕I)):= x ∘ Sum.inl
lemma second_lit (p)(x : Jets.Rays (V⊕I)): ContDiffAt ℝ p secondL x:= contDiffAt_pi.mpr fun _=> contDiffAt_apply ..
lemma first_lit (p)(x : Jets.Rays (V⊕I)): ContDiffAt ℝ p firstL x:= contDiffAt_pi.mpr fun _=> contDiffAt_apply ..
def oneStage (V I : Type*)[Fintype V][Fintype I]: Jets.Rays V→L[ℝ] Jets.Rays (V⊕I):= LinearMap.toContinuousLinearMap {
   toFun x:= Sum.elim x 0
   map_add' x y:= funext fun j=> by cases j <;> simp
   map_smul' x y:=funext fun j=> by cases j <;> simp }
def together (x: Jets.Rays I)(y:Jets.Rays V):= Sum.elim y x
omit [Fintype V][Fintype I] in @[simp] lemma unites (x:Jets.Rays I)(y: Jets.Rays V): secondL (together x y)=x:=rfl
omit [Fintype V][Fintype I] in @[simp] lemma pairs_with (x:Jets.Rays I)(y: Jets.Rays V): firstL (together x y)=y:=rfl
omit [Fintype V][Fintype I] in lemma toga (v : Jets.Rays (V⊕I)): together (secondL v) (firstL v)=v:=funext fun i=> by cases i <;> rfl
lemma tog_lit (b:Jets.Rays I)(x:Jets.Rays V): ContDiffAt ℝ ω (together b) x:= by refine contDiffAt_pi.mpr fun i=>?_ ; cases i <;> first| exact contDiffAt_const| exact contDiffAt_apply ..
lemma tog_rate (b:Jets.Rays I)(x:Jets.Rays V) : HasFDerivAt (together b) (oneStage V I) x:= by rw [show together b= (⇑(oneStage V I)+(fun _ => scalpel V I b) : Jets.Rays V→ Jets.Rays (V⊕I)) from funext fun j=> funext fun i=>by cases i <;> simp [together,oneStage,scalpel]];exact (oneStage V I).hasFDerivAt.add_const (scalpel V I b)
lemma together_dot (i:V): oneStage V I (dotI i)=dotI (Sum.inl i) := by ext1 j;cases j <;> simp [oneStage,dotI,Pi.single_apply]
-- restriction derivative. symmetry readability.
lemma tooth (f: Jets.Rays (V⊕I)→ℝ)(v:Jets.Rays V)(b:Jets.Rays I)(hp:DifferentiableAt ℝ f (together b v))(i) : pearlD f (.inl i) (together b v)= pearlD (f ∘ together b) i v:= by unfold pearlD; rw [(hp.hasFDerivAt.comp v (tog_rate b v)).fderiv]; simp only [ContinuousLinearMap.comp_apply,together_dot]
lemma puppy (f:Jets.Rays (V⊕I)→ℝ)(h:ContDiffAt ℝ ω f 0)(i j:V) : ∀ᶠ b in 𝓝 0, gateP f i j b= pearlD (pearlD (f∘together b) j) i 0:= by
    let g b:=f∘ together b; have hS:Tendsto (scalpel V I) (𝓝 0) (𝓝 0):= by simpa using (scalpel V I).continuous.tendsto 0
    let H:=pearlD f (Sum.inl j)
    have hx : ∀ᶠ x in 𝓝 0,DifferentiableAt ℝ H x := ((pearl_air f (.inl j) (h.of_le le_top)).of_le (show (2:WithTop ℕ∞)≤∞ by exact WithTop.coe_le_coe.mpr le_top) |>.eventually (by simp)).mono fun _ hp=>hp.differentiableAt (by norm_num)
    have hu : ∀ᶠ x in 𝓝 0,DifferentiableAt ℝ f x:= (h.eventually (by simp)).mono fun _ ht=> ht.differentiableAt (by simp)
    filter_upwards [hS.eventually (hx.and (eventually_eventually_nhds.mpr hu))] with b hh
    have hp:b=b:=rfl
    have h' : H ∘ together b=ᶠ[𝓝 (0:Jets.Rays V)] pearlD (f ∘ together b) j:= (((tog_lit b 0).continuousAt : ContinuousAt (together b) (0:Jets.Rays V)).eventually hh.2).mono fun y hy=> tooth f y b hy j
    change pearlD H (.inl i) (together b 0)=_; rw [tooth _ _ _ hh.1]; unfold pearlD; rw [Filter.EventuallyEq.fderiv_eq h'];rfl
lemma milk (f:Jets.Rays V→ℝ)(h: ContDiffAt ℝ ω f 0)(i j:V): pearlD (pearlD f j) i 0= iteratedFDeriv ℝ 2 f 0 ![dotI i,dotI j] := by
   -- use composition deriv next stage
   rw [iteratedFDeriv_two_apply]; unfold pearlD; let F:=fderiv ℝ f; have H: DifferentiableAt ℝ F 0:=(h.fderiv_right (m:=1) (by simp)).differentiableAt (by simp)
   let A:= (ContinuousLinearMap.apply ℝ ℝ (E:=Jets.Rays V) (dotI j));
   rw [show (fun x=> F x (dotI j))=A ∘ F from rfl,fderiv_comp _ (A.differentiableAt) H,A.fderiv];rfl

def boxcar (f:Jets.Rays I→Jets.Rays V)(x:Jets.Rays (V⊕I)) := firstL x+f (secondL x)
def Lshift (f:Jets.Rays I→ Jets.Rays V)(x:Jets.Rays (V⊕I)) := together (secondL x) (boxcar f x)
omit [Fintype V][Fintype I] in lemma coal_zero {f:Jets.Rays I→ Jets.Rays V}(h:f 0=0): Lshift f 0=0:= by unfold Lshift boxcar; rw [show secondL _=0 from rfl,h,add_zero]; ext1 i;cases i <;> rfl
lemma tilt_health {f:Jets.Rays I→ Jets.Rays V}(hp:ContDiffAt ℝ ω f 0): ContDiffAt ℝ ω (Lshift f) 0:= by
   have ht: ContDiffAt ℝ ω (f∘ secondL (V:=V)) 0:= ContDiffAt.comp _ hp (second_lit ..)
   refine contDiffAt_pi.mpr fun i=> ?_; cases i with
   | inl i=> exact (contDiffAt_pi.mp (show ContDiffAt ℝ ω (boxcar f) 0 from (first_lit ..).add ht) i)
   | inr i=> exact contDiffAt_apply ..
variable [DecidableEq V]
omit [DecidableEq V] in lemma money_roller (c:Jets.Rays I→ Jets.Rays V)(f:Jets.Rays (V⊕I)→ Jets.Rays V)(x:Jets.Rays (V⊕I))(h0:DifferentiableAt ℝ f (Lshift c x))(H:DifferentiableAt ℝ (Lshift c) x): dollars (f∘ Lshift c) x=dollars f (Lshift c x):= by
   let v:=firstL x; let b:=secondL x; let k := f∘ Lshift c
   have hp : x=together b v:=(toga x).symm
   have he: Lshift c ∘ together b =together b ∘ fun j=> j+c b:= by ext1 i; unfold Lshift boxcar; rw [Function.comp_apply]; simp only [unites, pairs_with];rfl
   have hw i: DifferentiableAt ℝ (fun z=>f z i) (Lshift c x) := differentiableAt_pi.mp h0 i
   have hq i: DifferentiableAt ℝ (fun z=>k z i) x:= (hw i).comp _ H
   ext1 i j
   change pearlD (fun z=> k z i) _ x= pearlD (fun z=> f z i) _ _; rw [hp,tooth _ _ _ (hp ▸ hq i)]
   have hd : DifferentiableAt ℝ (fun z=> f z i) (together b (v+c b)):= by rw [show together b (v+c b)=(Lshift c ∘ together b) v from congr_fun he.symm v, Function.comp_apply, ←hp]; exact hw i
   rw [show Lshift c _= together b (v+c b) from congr_fun he v,tooth _ _ _ hd]; let W:Jets.Rays V→Jets.Rays V:= fun j=> j+c b
   let U:= (fun z=>f z i) ∘ together b;rw [show (fun z=>k z i) ∘ together b= U ∘ W from funext fun i=> by rw [← show (fun i=>U (W i))=U ∘ W from rfl]; exact rfl] -- later
   have ha: HasFDerivAt W (ContinuousLinearMap.id ℝ (Jets.Rays V)) v := (hasFDerivAt_id v).add_const (c b)
   have hy : DifferentiableAt ℝ U (W v):= hd.comp _ (tog_rate _ _).differentiableAt; unfold pearlD; rw [fderiv_comp _ hy ha.differentiableAt,ha.fderiv]; rfl
end YM.FormalBulk08.Plait
