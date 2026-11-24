import YM.Contacts.Shuttle.Lagoon
/-! Radius Price in a finite direction panel. Propagates real invariant jets,
not assuming any horizontal estimate on the unselected interactions. -/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2000000
noncomputable section
namespace YM.Contacts.Shuttle.Tide
open Function Filter Finset Tensor Work Set MeasureTheory RG Wilson Lattice Labels Source Drops Analysis
open YM.MultiNext.SignedSource Powers Mediator Next.Foundations Pattern Broadcast Averaging
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{V E : Type*}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]{m n d h k:ℕ}
abbrev Draft (G:Gauge)(d:ℕ):= Stack G.Color d × Snap G d
abbrev Ship (G:Gauge)(κ:ℕ):= Axis→ Stack G.Color κ
-- interpolation allowance any headroom. Use also d^2 re economy. Tests of total weight ≤d use just d.
def glance (E:Type*) [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](h:ℕ)(x:E4): Stack E h→L[ℝ] E:= ((LinearMap.proj x).comp (glow E h)).toContinuousLinearMap
def shape (x:E4)(i:Axis) : Draft G d→L[ℝ] Panel G d :=
   let K(x:E4): Draft G d→L[ℝ] G.Color:= (glance G.Color d x).comp (ContinuousLinearMap.fst ℝ _ _)
   (K x).prod (((K (x+basis i))-(K x)).prod ((tempo x i).comp (ContinuousLinearMap.snd ℝ _ _)))
def shine (G:Gauge)(d:ℕ) (a:Draft G d)(x:E4)(i:Axis):= stereo G d (shape x i a)
lemma shape_sound (a:Draft G d)(x:E4)(i):shape x i a= sight x i (glow G.Color d a.1) a.2:=rfl
lemma shine_germ (x:E4)(i:Axis): ContDiffAt ℝ ω (fun a:Draft G d=> shine G d a x i) 0:=
   (show ContDiffAt ℝ ω (stereo G d) (shape (G:=G) (d:=d) x i 0) from by rw [show shape x i 0= (0: Panel G d) from (shape (G:=G) (d:=d) x i).map_zero]; exact (scripts G d).1).comp 0 (shape (G:=G) (d:=d) x i).contDiff.contDiffAt
@[simp] lemma shine_zero (G:Gauge)(d:ℕ)(x:E4)(i:Axis): shine G d 0 x i=0:= by rw [shine,show shape x i 0=(0:Panel G d) from (shape (G:=G) (d:=d) x i).map_zero]; exact (scripts G d).2
lemma derivative_shine (x:E4)(i:Axis) (v:Fin m→Draft G d):
   iteratedFDeriv ℝ m (fun a=> shine G d a x i) 0 v=iteratedFDeriv ℝ m (stereo G d) 0 (fun j=> sight x i (glow G.Color d (v j).1) (v j).2):=
      congr_arg (fun f:T (Draft G d) G.Color m=> f v) (Next.Foundations.jets_linear (shape (G:=G) (d:=d) x i) ((scripts G d).1.of_le le_top))
def rain (G:Gauge)(d k:ℕ)(a:Draft G d): Ship G k:= fun i=> fit k (fun x=> shine G d a x i)
private lemma germ_rain_axis (x:Axis): ContDiffAt ℝ ω (fun a:Draft G d=> rain G d k a x) 0:= (stars G.Color k).interpolate.contDiff.contDiffAt.comp (f:=fun a:Draft G d=> fun i:(stars G.Color k).nodes=> shine G d a i x) 0 (contDiffAt_pi.mpr fun _=> shine_germ ..)
lemma germ_rain (G:Gauge)(d k:ℕ): ContDiffAt ℝ ω (rain G d k) 0:= contDiffAt_pi.mpr germ_rain_axis
@[simp] lemma rain_base (G:Gauge)(d k):rain G d k 0=0:= by funext i; unfold rain fit; simp [shine_zero]; exact (stars G.Color _).interpolate.map_zero
lemma derivative_rain (k:ℕ)(x:Axis)(v: Fin m→ Draft G d):
    iteratedFDeriv ℝ m (rain G d k) 0 v x=fit k (fun y=> iteratedFDeriv ℝ m (stereo G d) 0 (fun j=> sight y x (glow G.Color d (v j).1) (v j).2)):= by
   let i:= stars G.Color k; let p(a:Draft G d)(s:i.nodes):= shine G d a s x; let P(s:i.nodes): (i.nodes→ G.Color)→L[ℝ] G.Color:= ContinuousLinearMap.proj s; let Y: Ship G k→L[ℝ] Stack G.Color k:= ContinuousLinearMap.proj x; have he:= Y.iteratedFDeriv_comp_left (germ_rain G d k) (i:=m) le_top; let f:= Y ∘ rain G d k
   have hh : ContDiffAt ℝ ω p 0:= contDiffAt_pi.mpr (fun s=> shine_germ ..); have ht : Y ∘ rain G d k=i.interpolate ∘ p:= rfl
   rw [ht,i.interpolate.iteratedFDeriv_comp_left hh] at he; rotate_left; · exact le_top
   rw [show _=_ from (show iteratedFDeriv ℝ m (rain G d k) 0 v x=i.interpolate (iteratedFDeriv ℝ m p 0 v) from (DFunLike.congr_fun he v).symm)]; apply congr_arg i.interpolate; funext z; have hz := (P z).iteratedFDeriv_comp_left hh (i:=m) le_top; exact ((DFunLike.congr_fun hz v).symm.trans (derivative_shine z x v))
def Jar (G:Gauge)(d b:ℕ): Submodule ℝ (Draft G d) where
  carrier:={x|glow G.Color d x.1∈Powers.space E4 G.Color b ∧ ∀ i: Fin (d-1), b < i.val+2→ x.2 i=0}
  zero_mem':=⟨by rw [show (0:Draft G d).1=0 from rfl,map_zero]; exact (Powers.space E4 G.Color _).zero_mem, fun _ _=>rfl⟩
  add_mem' {v y} hv hy:= ⟨by rw [Prod.fst_add,map_add]; exact (Powers.space E4 G.Color _).add_mem hv.1 hy.1, fun i h=> by rw [Prod.snd_add,Pi.add_apply,hv.2 _ h,hy.2 _ h,zero_add]⟩
  smul_mem' c v hv:= ⟨by rw [Prod.smul_fst,map_smul]; exact (Powers.space E4 G.Color _).smul_mem _ hv.1, fun i h=> by rw [Prod.smul_snd,Pi.smul_apply,hv.2 _ h, smul_zero]⟩
def Draws (G:Gauge)(k b:ℕ): Set (Ship G k) := {x|∀ i, ∃ f:E4→G.Color,f∈Powers.space E4 G.Color (b-1) ∧ x i= fit k f}
lemma rain_health (he:d≤k): curry (fun i=>(Jar G d i:Set _)) (Draws G k) d (rain G d k):= by
    intro m hm a v ha i; rw [derivative_rain]; exact ⟨_,channel m i _ _ a (fun j=> ((ha.1 j).2 : _ ∈ Jar G d (a j)).1) (fun j=> ((ha.1 j).2 : _ ∈ Jar G d (a j)).2) (fun j=> (ha.1 j).1),rfl⟩ -- fill
lemma derivative_glow (v:Fin m→ Draft G d)(x:E4)(i:Axis)(a:Fin m→ℕ)(ha:∀ j,1 ≤ a j ∧ v j ∈ Jar G d (a j))(hk:(∑ j,a j)-1 ≤k):
    glow G.Color k (iteratedFDeriv ℝ m (rain G d k) 0 v i) x= iteratedFDeriv ℝ m (fun f=> shine G d f x i) 0 v:= by
   rw [derivative_rain,derivative_shine,sky]; refine Powers.widen _ _ hk (channel m i _ _ a (fun i=>?_ ) (fun i=>?_) (fun i=>(ha i).1)); exacts [((ha _).2: _).1,((ha _).2:_).2]
end YM.Contacts.Shuttle.Tide
