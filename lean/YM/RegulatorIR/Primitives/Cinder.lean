import YM.RegulatorIR.Primitives.Firn

/-!
Unfold Wilson blocking penalty primitive. Native predictor computed from genuine
patch paths; relation to ANY compatible finite underlying torus, including all
possible windings. Draw branch angles in actual Gauge. No mask assertion. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Prim
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory MvPolynomial Cluster Diagram Quadratic Lattice Wilson Geometry Chart Gauge RG Orb Laplace Tree
open scoped Topology ENNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {I J X:Type}{G:Gauge}{k a b:ℕ}{f c: Side}
variable (A : Patch)(C:KernelChoices)
-- uses fixed common choices but coarsest representative V native. identical germ for any. x+(a,b) fine.

def readsE (A:Patch)(C:KernelChoices) (x: Cover) (U:CoverConfig G): A.Frame G := A.frame C (translate (A.L.val • x) U) (A.center,Equiv.refl _)
def knotE (i:Edge Cover)(U:CoverConfig G):A.Connector G:=fun x=> readsE A C i.1 U x*travel (translate (A.L.val • i.1) U) x.val (List.replicate A.L.val (posDir i.2))*(readsE A C (i.1+step i.2) U x)⁻¹
def pond (U:CoverConfig G)(i:Edge Cover) : G.El:= A.predict C (knotE A C i U) A.center

section Brick
variable {S: StepData c f}(U: Config G f)
lemma bring (x:Cover): translate (S.patch.L.val • x) (U ∘ around f)=expandAt (S.ratio.embed (wrap c x)) U:=by
 ext1 i; unfold translate around expandAt; rw [Function.comp_apply];dsimp only; rw [map_add,Ratio.embed_wrap];rfl
lemma river (i:Edge Cover) : pond S.patch S.kernel (U ∘ around f) i= S.prediction U (directive S) (around c i):=by
 unfold pond StepData.prediction; apply congr_arg (fun v=> S.patch.predict _ v S.patch.center);ext1 x
 unfold knotE readsE StepData.connector StepData.frames; simp_rw [bring (S:=S), map_add,wrap_step];rfl
end Brick

-- depends only on finite box. Need not use Step.G.branch uniqueness? selected minimizer by proof irrelevance choose once. show mathematically safe with H.
section Support
variable (H:A.Branches C G)
def tiny (A:Patch): Finset (Edge Cover):= Finset.univ.biUnion (fun i:A.Points × A.Points × Lattice.Order=> steps i.1.val (route i.1.val i.2.1.val i.2.2))
include H in
lemma root_low (i:A.FrameTag) : Names (fun u:CoverConfig G=> A.frame C u i) (tiny A):=by
 let X:=tiny A; intro v w h
 have hp (x y : A.Points) (l:Lattice.Order): travel v x.val (route x.val y.val l)=travel w x.val (route x.val y.val l) :=travel_knows x.val _ _ _ fun e hh=> h e (Finset.mem_biUnion.mpr ⟨(x,y,l), Finset.mem_univ _,hh⟩)
 have ht b : A.axial v b=A.axial w b:= by ext1 x; exact hp ..
 have hs (u:A.Frame G) (x y l): A.via u v x y l= A.via u w x y l:=by rw [Patch.via,Patch.via,hp]
 have hh : A.usesMin C v=A.usesMin C w:=by unfold Patch.usesMin; simp_rw [← ht,hs]
 unfold Patch.frame; dsimp only; rw [hh]; split
 next hx=>
    have hχ (u:A.Frame G) : A.score v u=A.score w u:=by unfold Patch.score; simp_rw [hs]
    refine (H.frame_unique w hx).unique ?_ (A.min_exists _).choose_spec
    have HV:= (A.min_exists v).choose_spec; change A.minimizing v (A.selected v) at HV; unfold Patch.minimizing at *; simp_rw [hχ] at HV;exact HV
 rw [ht]
-- shift paths

def rangeE (r:Cover)(K:Finset (Edge Cover)): Finset (Edge Cover):= K.image (Geometry.dis r)
lemma shifted {F: CoverConfig G → X}{r:Finset (Edge Cover)}(h:Names F r)(p:Cover): Names (fun U=>F (translate p U)) (rangeE p r):=by
 intro i j H; apply h;intro x hx; unfold Lattice.translate; rw [add_comm x.1]; exact H (dis p x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)

include H in
lemma reads_low (p:Cover): Names (readsE A C p (G:=G)) (rangeE (A.L.val • p) (tiny A)):=shifted (root_low A C H (A.center,Equiv.refl _)) _
def lantern (x:Edge Cover) : Finset (Edge Cover):= (rangeE (A.L.val • x.1) (tiny A) ∪ rangeE (A.L.val • (x.1+step x.2)) (tiny A)) ∪ Finset.univ.biUnion fun p:A.Points=> rangeE (A.L.val • x.1) (steps p.val (List.replicate A.L.val (posDir x.2)))
include H
lemma pond_low (x:Edge Cover): Names (fun U:CoverConfig G=>pond A C U x) (lantern A x):= by
 intro i j h; unfold pond; apply congr_arg (fun v=> A.predict C v _); ext1 p
 have hp: readsE A C x.1 i= readsE A C x.1 j:= reads_low A C H x.1 i j (fun z ht=> h z (Finset.mem_union_left _ (Finset.mem_union_left _ ht)))
 unfold knotE;rw [hp]
 let s:=x.1+Lattice.step x.2
 rw [show readsE A C (x.1+step x.2) i=readsE A C s j from reads_low A C H s i j (fun z ht=>h z (Finset.mem_union_left _ (Finset.mem_union_right _ ht)))]
 let l:=List.replicate A.L.val (posDir x.2)
 have hx:= shifted (travel_knows (G:=G) p.val l) (A.L.val • x.1) i j (fun z he=>h z (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p,Finset.mem_univ _,he⟩)))
 change _*travel _ _ l*_= _; rw [show travel (translate _ i) p.val l= travel (translate _ j) p.val l from hx]
end Support

-- projection to arbitrary much larger plank of same algorithm

def canopy (S:StepData c f)(n:Side): StepData n (n*S.patch.L):= { patch:= S.patch,kernel:=S.kernel,sizes:=rfl }
lemma sunset (S:StepData c f)(n:Side)(U:Config G (n*S.patch.L))(x) : pond S.patch S.kernel (U ∘ around (n*S.patch.L)) x=(canopy S n).prediction U (directive (canopy S n)) (around n x):=river (S:=canopy S n) ..

def ascend (R:Finset (Edge Cover)) (f:Side) (h:Set.InjOn (around f) (R:Set (Edge Cover))) : ↥R↪ Edge (Site f):=⟨fun i=>around f i.val, fun i j hj=>Subtype.ext (h i.property j.property hj)⟩
lemma ampleS (A:Patch)(R:Finset (Edge Cover)): ∃ n:Side, InjOn (around (n*A.L)) (R:Set (Edge Cover)):=by
 let s : Finset (Cover × Axis):=R; let K:=R.sup fun i=> Finset.univ.sup fun a=> (i.1 a).natAbs
 let n:Side:=⟨2*K+4,by omega⟩; let f:=n*A.L
 have hz: n.val ≤ f.val := le_mul_of_one_le_right (by omega) (by have := A.L.property;omega)
 have hp (v) (hv:v∈R) :∀ i: Axis,-(f.val:ℤ) < 2*v.1 i ∧ 2*v.1 i ≤ f.val:=by
    intro j; have h: (v.1 j).natAbs ≤ K:= (Finset.le_sup (f:=fun i=>(v.1 i).natAbs) (Finset.mem_univ j)).trans (Finset.le_sup (f:=fun i:Edge Cover=> Finset.univ.sup fun a=> (i.1 a).natAbs) hv)
    have he:n.val=2*K+4:=rfl;omega
 exact ⟨n,fun _ i _ j h=> Prod.ext (wrap_injOn f (hp _ i) (hp _ j) (congr_arg Prod.fst h)) (congr_arg (Prod.snd : Edge (Site f) → Axis) h)⟩
lemma apod {S: Finset (Edge Cover)}{f : Side}(h:Set.InjOn (around f) (S:Set (Edge Cover)))(U:CoverConfig G):∃ V : Config G f,∀ i∈S,U i=(V ∘ around f) i:=by
 let g:=ascend S f h; exact ⟨Function.extend g (fun i=> U i.val) (fun _=>1),fun i hi=> (g.injective.extend_apply (e':=fun _=>1) (g:=fun i=>U i.val) ⟨i,hi⟩).symm⟩

-- shifts & inversion
lemma pulled {S:StepData c f}(x:Cover)(U:CoverConfig G) : pond S.patch S.kernel (translate (S.patch.L.val • x) U)= translate x (pond S.patch S.kernel U):=by
 -- plain translated reads arithmetic
 ext1 i; unfold Lattice.translate; unfold pond; apply congr_arg (fun v=> S.patch.predict S.kernel v _); ext1 p; unfold knotE readsE
 -- U (e+x) repeated
 have he (z: Cover): translate (S.patch.L.val • z) (translate (S.patch.L.val • x) U)=translate (S.patch.L.val • (z+x)) U:=by ext1 i; simp [translate,smul_add,add_assoc]
 -- convert nested defeq
 change _*travel (translate _ (translate _ U)) _ _ * _= _
 -- rew unknown z need explicit
 rw [he i.1,show i.1+x+step i.2= i.1+step i.2+x by abel]; change S.patch.frame _ (translate _ (translate _ U)) _ _ * _ * (S.patch.frame _ (translate _ (translate _ U)) _ _)⁻¹=_; rw [he i.1,he (i.1+step i.2)] -- maybe first rew did both

lemma chilled {S:StepData c f}(H:S.patch.Branches S.kernel G)(U:CoverConfig G) (i:Edge Cover) : pond S.patch S.kernel (pull invS 0 U) i=(pond S.patch S.kernel U (reco i))⁻¹:=by
 have hc (W:CoverConfig G) (v:Edge Cover):pull invS 0 W v=(W (reco v))⁻¹:=by rw [pull,affine,pivot_dir,add_zero];rfl
 let L:=S.patch; let A:= lantern L i; let R:= A.image reco∪ lantern L (reco i)
 obtain ⟨n,h⟩:= ampleS L R;obtain ⟨V,hv⟩:= apod h U
 let K:= canopy S n;let T:= pond (G:=G) L S.kernel;have hh:K.patch.Branches K.kernel G:=H
 let F:=n*L.L;let W:= pull invS 0 V
 have he:= K.prediction_channel hh invS 0 V (directive K)
 rw [directs, show K.ratio.embed 0=0 from K.ratio.root.map_zero] at he
 have hs : T (pull invS 0 U) i= (K.prediction W (directive K) (around n i)):=by
    rw [← sunset S n W]; apply pond_low S.patch S.kernel H i
    intro z hz; rw [hc U]; change _= W _;rw [hv (reco z) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨z,hz,rfl⟩)), Function.comp_apply,reco_edge]
    exact (spun ..).symm
 have hx:T U (reco i)=K.prediction V (directive K) (around n (reco i)):=by
    rw [← sunset S n V]; apply pond_low _ _ H _ U (V ∘ around F) (fun i hi=>hv _ (Finset.mem_union_right _ hi))
 change T _ i= (T U (reco i))⁻¹; rw [hs,hx]; unfold W; rw [he, reco_edge, spun]
end YM.RegulatorIR.Prim
