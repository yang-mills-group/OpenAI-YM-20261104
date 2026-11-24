import YM.OPE.Compatible.Estuary.Lance
/-! # Tape collective gauge-shift on ALL logs of pitch. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Votive Tree
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n c f:Side} {P:Patch}
namespace Script
open Page Virgin
variable (G)
def stave : Finset (Cover×Blend G):= (insert 0 (univ.image (fun i:Axis=>step i))) ×ˢ univ
abbrev climate:= shelf (stave G)
abbrev notchS (x: Cover×Blend G)(p:climate G):ℝ:= if h:x∈stave G then p ⟨x,h⟩ else 0
def ups (x:Cover):climate G→L[ℝ] G.Color:=LinearMap.toContinuousLinearMap {
   toFun p:= toLp 2 fun j=> notchS G (x,.inr j) p
   map_add' p q:=by ext j; by_cases ht:(x,Sum.inr j)∈stave G<;>simp [notchS,ht]
   map_smul' c p:=by ext j; by_cases ht:(x,Sum.inr j)∈stave G<;>simp [notchS,ht]}
def psc (x:Axis):climate G→L[ℝ] G.Color:= LinearMap.toContinuousLinearMap {
   toFun p:= toLp 2 fun j=> p ⟨(0,Sum.inl (x,j)),by simp [stave]⟩
   map_add' p q:=rfl
   map_smul' p q:=rfl }
def hut (p:climate G) (i:Axis):= G.lieExp (-ups G 0 p)*G.lieExp (psc G i p)*(G.lieExp (-ups G (step i) p))⁻¹
def vigil (i:Blend G)(x:climate G):ℝ:= i.elim (fun i=> (plogC G (hut G x i.1)) i.2) (fun _=>0)
lemma hut_zero : hut G 0=1:=by funext i; simp [hut]
lemma hutA : Army (hut G) 0:=by
    let H(p:climate G)(i:Axis):= G.lieExp (-ups G (step i) p); let F x:= fun p:climate G=>G.lieExp (-ups G x p); have he(x): ContDiffAt ℝ ω (fun p=>G.mat (F x p)) 0:= G.exp_jet.contDiffAt.comp (f:=fun p: climate G=> -(ups G x p)) 0 (ups G x).contDiff.contDiffAt.neg; have hv : Army H 0:=fun i=> he _; exact Army.mul (u:=fun p i=> F 0 p*G.lieExp (psc G i p)) (v:=fun p=>(H p)⁻¹) (fun i=> (he 0).mul (G.exp_jet.contDiffAt.comp (f:= psc G i) _ (psc G i).contDiff.contDiffAt)) hv.inv
lemma vigilA (i:Blend G):vigil G i 0=0∧ ContDiffAt ℝ ω (vigil G i) 0:=by
    rcases i with ⟨i,j⟩|i; swap; · exact ⟨rfl,contDiffAt_const⟩
    constructor
    · change plogC G (hut G 0 _) _= _; rw [hut_zero,Pi.one_apply,show plogC G (1:G.El)=0 from plogC_one]; rfl
    let F:= fun x=> G.mat (hut G x i); have he : F 0=1:=by unfold F; rw [hut_zero]; exact G.mat_one
    have hh :ContDiffAt ℝ ω (G.plog ∘ F) 0:=(he.symm ▸ G.plog_diff : ContDiffAt ℝ ω G.plog (F 0)).comp _ (hutA G i); exact (EuclideanSpace.proj j ).contDiff.contDiffAt.comp _ hh
abbrev fog (n:Side): deck (Blend G) n→deck (Blend G) n:= vitalX (stave G) (vigil G)
abbrev lac (n:Side): deck (Blend G) n→L[ℝ] deck (Shade G) n:= ContinuousLinearMap.pi fun i:Tab (Shade G) n=> ContinuousLinearMap.proj (starI i)
abbrev solidY (n:Side): deck (Blend G) n→L[ℝ] Bid.Dir G n:= (spool G n).symm.toContinuousLinearMap ∘L lac G n
lemma phase_read (j: Edge (Site n))(x:deck (Blend G) n): psc G j.2 (lookS (stave G) j.1 x)=solidY G n x (j.1,coord j.2):=by ext a; change x (j.1+wrap n 0,_)=x (starI (j.1,axisEquiv.symm (axisEquiv j.2),a));rw [Equiv.symm_apply_apply,map_zero,add_zero]
lemma attic (j:Axis)(i:Site n)(x:deck (Blend G) n): ups G (step j) (lookS (stave G) i x)=ups G 0 (lookS (stave G) (i+step j) x):= by
   ext a; change notchS ..=notchS ..; unfold notchS; rw [dif_pos,dif_pos]; rotate_left; · simp [stave]
   · simp [stave]
   change x (i+wrap n (step j),_)=x ((i+step j)+wrap n 0,_); rw [wrap_step, map_zero,add_zero]
def plover (x:deck (Blend G) n)(i:Site n):G.El:=G.lieExp (-ups G 0 (lookS (stave G) i x))
lemma hut_stand (x:deck (Blend G) n)(i: Edge (Site n)): hut G (lookS (stave G) i.1 x) i.2= Lattice.gauge (plover G x) (represent (solidY G n x)) i:=by
    unfold hut; rw [phase_read _ i, attic]; simp only [Lattice.gauge,plover,Work.F03.represent_link]
lemma fogDial (n:Side): fog G n 0=0∧ContDiffAt ℝ ω (fog G n) 0:= ⟨funext fun i=>by change vigil G i.2 (lookS _ i.1 0)=0; rw [map_zero]; exact (vigilA G _).1, ledgeDiff _ _ (fun i=> (vigilA G i).2) n⟩
lemma fog_gr (n:Side): ∀ᶠ v:deck (Blend G) n in 𝓝 0,represent (solidY G n (fog G n v))=Lattice.gauge (plover G v) (represent (solidY G n v)):=by
   have h(i:Edge (Site n)):∀ᶠ v:deck (Blend G) n in 𝓝 0,represent (solidY G n (fog G n v)) i=Lattice.gauge (plover G v) (represent (solidY G n v)) i:=by
       let T(v:deck (Blend G) n):= hut G (lookS (stave G) i.1 v) i.2; let F:= lookS (stave G) i.1
       have he : Tendsto T (𝓝 0) (𝓝 1):=(tendsto_pi_nhds.mp (hut_zero G ▸ (hutA G).cont.tendsto) i.2).comp (F.map_zero ▸ F.continuous.tendsto 0)
       filter_upwards [he.eventually G.plog_right] with v hv; have hf: solidY G n (fog G n v) (i.1,coord i.2)= G.plog (G.mat (T v)):=by rw [← phase_read]; ext a; change fog G n v (i.1+wrap n 0,.inl (i.2,a))=_; rw [map_zero,add_zero]; rfl
       erw [Work.F03.represent_link,hf,← hut_stand]; exact hv
   exact (eventually_all.mpr h).mono fun v hv=> funext hv
end Script
end YM.OPE.Flume
