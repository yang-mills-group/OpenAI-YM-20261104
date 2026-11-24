import YM.SchemeRG11.Saddle.Legato
/-! Ghost comparator. On Landau only one can project to Mean rather
than rooted site parameters, precisely because of the even CONSTANT gauge (fixes
entire slice). Our Target MSbar uses mean ghosts in the adapt. Lattice div is NOT
gauge covariant generally, so we check the whole germ identity; not comparing
 the individual off-shell ghost spectra across quotients.
-/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.SchemeRG11.Sway
open scoped Classical ContDiff Topology Matrix.Norms.Frobenius
open Function Filter Lattice Pert.Orb PertExtension.Orb LocalH MeasureTheory Precision Push.Loops
variable {G:Gauge}{n:Side}
abbrev AllSite (G:Gauge)(n:Side):= ↥(EvenSite G n)
def firmL: Parameter G n→L[ℝ] AllSite G n:= (Submodule.inclusion (show Pert.Orb.Zero G n ≤ EvenSite G n from inf_le_left)).toContinuousLinearMap
def shoreL: ↥(Flow G n)→L[ℝ] AllSite G n:= (Submodule.inclusion (show Mean G n≤ EvenSite G n from inf_le_left)).toContinuousLinearMap

def roughM(a:Potential G n)(z: AllSite G n) (l:Pert.Orb.Links n):= G.plog (G.mat (Lattice.gauge (fun i : Site n=>G.lieExp (z.val i)) (positiveLinks a) l))
def logM(a:Potential G n)(z:AllSite G n):= balance G n (roughM a z)
def DivM(a:Potential G n)(z: AllSite G n):= dLin (logM a z)
lemma roughM_slick : ContDiffAt ℝ ω (fun p : Potential G n × AllSite G n=> roughM p.1 p.2) 0:=by
 let X (i:Site n)(p:Potential G n×AllSite G n):= G.lieExp (p.2.val i)
 have hX(i:Site n): ContDiff ℝ ω (fun p=> G.mat (X i p)):=by
    let L:Potential G n × AllSite G n→L[ℝ]G.Color:= ((LinearMap.proj (R:=ℝ) i) ∘ₗ ((EvenSite G n).subtype) ∘ₗ LinearMap.snd ℝ _ _).toContinuousLinearMap
    exact ContDiff.comp (g:=fun x=>G.mat (G.lieExp x)) (f:=L) G.exp_jet L.contDiff
 apply contDiffAt_pi.mpr; intro l
 let f(p:Potential G n × AllSite G n):= Lattice.gauge (fun i : Site n=>X i p) (positiveLinks p.1) l
 have he:ContDiffAt ℝ ω (fun p=>G.mat (f p)) 0:=by
    unfold f Lattice.gauge; simp only [G.mat_mul]; exact (((hX _).contDiffAt).mul ((pos_mDiff _).comp contDiff_fst).contDiffAt).mul (mat_inv_diff (hX _).contDiffAt)
 exact ContDiffAt.comp (f:=fun p=>G.mat (f p)) (g:=G.plog) 0 (by rw [show f 0=1 by simp [f,X,Lattice.gauge],G.mat_one]; exact G.plog_diff) he
lemma DivM_slick: ContDiffAt ℝ ω (fun p:Potential G n × AllSite G n=> DivM p.1 p.2) 0:=by
 let L := divL G n ∘L (balance G n).toContinuousLinearMap
 have h: ContDiff ℝ ω L:=ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Pert.Orb.Links n→G.Color) (F:= ↥(Flow G n)) L
 exact h.contDiffAt.comp (f:=fun p:Potential G n × AllSite G n=>roughM p.1 p.2) 0 roughM_slick

def stump (G:Gauge)(n:Side): G.Color→L[ℝ] AllSite G n:= LinearMap.toContinuousLinearMap ((LinearMap.pi fun _:Site n=>LinearMap.id (R:=ℝ) (M:=G.Color)).codRestrict (EvenSite G n) (fun _ _=>rfl))
lemma stump_apply(a:G.Color)(i:Site n):(stump G n a).val i=a:=rfl
lemma root_constant_near: ∀ᶠ p:Land G n × G.Color in 𝓝 0, DivM p.1.val (stump G n p.2) =0 :=by
 let f(p:Land G n × G.Color)(l:Pert.Orb.Links n):= G.adjoint (G.lieExp p.2) (p.1.val.val l)
 have h(i:Pert.Orb.Links n): Tendsto (fun p=>f p i) (𝓝 0) (𝓝 0):=by
    let L:= ((takeLink (G:=G) i).toContinuousLinearMap ∘L (g0 G n)) ∘L ContinuousLinearMap.fst ℝ (Land G n) G.Color
    have he: ContDiffAt ℝ ω (fun p=>f p i) 0:= by exact adjoint_diff (u:=fun p:Land G n× G.Color=>G.lieExp p.2) (a:=L) ((G.exp_jet.comp (f:=Prod.snd) contDiff_snd).contDiffAt) ((ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Land G n×G.Color) (F:=G.Color) L).contDiffAt) -- fix implicit
    simpa only [show f 0 i=0 by unfold f; change G.adjoint _ (0:G.Color)=_; rw [map_zero]] using he.continuousAt.tendsto
 have H: ∀ᶠ p:Land G n × G.Color in 𝓝 0, ∀ i:Pert.Orb.Links n, G.plog (G.mat (G.lieExp (f p i)))=f p i:= eventually_all.mpr fun i=>(h i).eventually G.plog_left
 filter_upwards [H] with p hp
 have hf: roughM p.1.val (stump G n p.2)=f p:=by
    funext l; have he:=hp l; unfold f at *; unfold roughM; simp only [Lattice.gauge,stump_apply,positiveLinks,←exp_adjoint]; exact he
 let v: Potential G n:= ⟨f p, fun l=>by unfold f; rw [p.1.val.property l,map_neg]⟩
 have hv: logM p.1.val (stump G n p.2)= v:= by rw [logM,hf]; exact balance_same v
 unfold DivM; rw [hv]; apply Subtype.ext; funext i
 change ∑ l:Axis,(v.val (i,l)-v.val (i-step l,l))=0
 change (∑ l:Axis,(f p (i,l)-f p (i-step l,l)))=0; unfold f; simp only [← map_sub,← map_sum]
 rw [show (∑ l:Axis,(p.1.val.val (i,l)-p.1.val.val (i-step l,l)))=0 from congrFun (congrArg Subtype.val (div_trans p.1)) i,map_zero]

def buckle (G:Gauge)(n:Side): ↥(Flow G n)→ₗ[ℝ]Parameter G n:=
  let L:= LinearMap.pi (fun x:Site n=> (LinearMap.proj (R:=ℝ) x - LinearMap.proj (R:=ℝ) (φ:=fun _ : Site n=>G.Color) 0).comp (Flow G n).subtype)
  LinearMap.codRestrict (Pert.Orb.Zero G n) L (fun a=> ⟨fun x=> by exact congrArg (·-a.val 0) ((show _ ∧ _ from a.property).1 x),show (L a) 0=0 from by exact sub_self _⟩)
lemma buckle_bridge(a:↥(Flow G n)):gZ (buckle G n a)=gM a:=by apply Subtype.ext; funext l; change (a.val l.1-_) - (a.val _ -_)=a.val l.1-a.val _; change (a.val l.1-a.val 0) - (a.val _-a.val 0)=_; simp

def buckleE(G:Gauge)(n:Side): ↥(Flow G n)≃L[ℝ]Parameter G n:=
 let L:=buckle G n
 have hi:Injective L:=fun a b h=> mean_inj (congrArg (dLin (G:=G) (n:=n)) ((buckle_bridge a).symm.trans <| (congrArg gZ h).trans (buckle_bridge b)))
 (LinearEquiv.ofBijective L ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ((spanLink G n).toLinearEquiv.symm.finrank_eq)).mp hi⟩).toContinuousLinearEquiv
lemma buckle_eq(a:↥(Flow G n)): shoreL a= firmL (buckleE G n a)+stump G n (a.val 0):= by apply Subtype.ext; funext x; change a.val x=(a.val x - a.val 0)+a.val 0; rw [sub_add_cancel]

def paneGhost(G:Gauge)(n:Side) (t:Land G n): ↥(Flow G n)→L[ℝ] ↥(Flow G n):= fderiv ℝ (DivM t.val ∘ shoreL) 0
def paneLap (G:Gauge)(n:Side): ↥(Flow G n)≃L[ℝ] ↥(Flow G n):= (buckleE G n).trans (spanLink G n)
lemma paneLap_eq(a:↥(Flow G n)): paneLap G n a= dLin (gM a):= by change dLin (gZ (buckle G n a))=_; rw [buckle_bridge a]
lemma derived_ghost: ∀ᶠ p:Land G n in 𝓝 0,paneGhost G n p = FPDeriv p.val ∘L (buckleE G n).toContinuousLinearMap:= by
 let L:=g0 G n
 have ht1:Tendsto (fun p:Land G n=>(p,(0:G.Color))) (𝓝 0) (𝓝 0):=tendsto_id.prodMk_nhds tendsto_const_nhds
 have ht:Tendsto (fun p:Land G n=>(p.val,(0:AllSite G n))) (𝓝 0) (𝓝 0):= by exact (L.continuous.continuousAt (x:=0)).tendsto.prodMk_nhds tendsto_const_nhds
 filter_upwards [ht.eventually ((DivM_slick (G:=G) (n:=n)).eventually (by simp)), ht1.eventually (eventually_eventually_nhds.mpr root_constant_near)] with p hp he
 let f:= DivM p.val
 have hu: ContDiffAt ℝ ω f 0:=ContDiffAt.comp (f:=fun z:AllSite G n=>(p.val,z)) 0 hp (contDiffAt_const.prodMk contDiffAt_id)
 let M:= fderiv ℝ f 0
 have hc{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](u:E→L[ℝ] AllSite G n): fderiv ℝ (f ∘ u) 0=M ∘L u:=by rw [fderiv_comp 0 (by rw [map_zero]; exact hu.differentiableAt (by simp)) u.differentiableAt,map_zero,u.fderiv]
 let P:= stump G n
 have hz: M ∘L P=0:=by
    have hv:Tendsto (fun x:G.Color=>(p,x)) (𝓝 0) (𝓝 (p,0)):=tendsto_const_nhds.prodMk_nhds tendsto_id
    rw [← hc]
    have hi: f ∘ P=ᶠ[𝓝 0] fun _=> (0: ↥(Flow G n)):= (hv.eventually he); rw [hi.fderiv_eq]; simp
 have hF: M ∘L firmL = FPDeriv p.val:=by rw [← hc]; rfl
 unfold paneGhost; rw [hc,← hF]; apply ContinuousLinearMap.ext; intro a
 change M (shoreL a)= M (firmL (buckleE G n a)); rw [buckle_eq a,map_add, show M (stump G n _)=0 from DFunLike.congr_fun hz (a.val 0),add_zero]
lemma pane_flat: paneGhost G n 0 = (paneLap G n).toContinuousLinearMap:=by
 rw [mem_of_mem_nhds (s:={p|paneGhost G n p= FPDeriv p.val ∘L (buckleE G n).toContinuousLinearMap}) derived_ghost,Submodule.coe_zero,FPDeriv_flat];rfl
lemma pane_agrees:∀ᶠ p:Land G n in 𝓝 0,FP p.val=((paneLap G n).symm.toContinuousLinearMap ∘L paneGhost G n p).det:=by
 filter_upwards [derived_ghost] with p hp
 let e:=buckleE G n
 rw [coat_rate,hp]; change _ = LinearMap.det _
 symm; exact LinearMap.det_conj (resetFP p.val).toLinearMap e.symm.toLinearEquiv
end YM.SchemeRG11.Sway
