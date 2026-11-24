import YM.WilsonBridge.ProjectionCov
import YangMills.WilsonProof.NativeSupport.YM.Extra.WEAK_SCALING_ACTLAW.Color
/-!
# Position to quotient ink, global coset handling

When a mean-zero ghost is written as the based ghost PLUS a global rotation
field (constant determined by the based field), its coupling to A transforms.
Compute the difference here as a germ; no range choice/prepayment. The same pull
computes the full Wilson log and log Haar factors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge.Injections
open MS MS.Book MS.Koszul MS.City MS.Native MS.Tone MS.Plane Lattice MS.Orbit MS.Landau MS.Bare MS.Cylinder MS.Swirl
open Function Finset Full Based Based.Position Matrix Taylor Filter PertExtension Orb
open scoped BigOperators Matrix Topology Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side}
local notation "GJ" => Position.Gluon G n
local notation "GC" => Position.Ghost G n
local notation "π"=> Position.Parity G n
local notation "L"=> Position.Letter G n
local notation "P"=> Position.E G n
local notation "V"=> Full.Index G n
local notation "J"=> Full.Glu G n
local notation "C"=> Full.Ghost G n
local notation "T"=> aFull G n
local notation "η"=> liftA G n
local notation "Uₐ"=> Ux G n
local notation "Ω"=> cLift G n
local notation "χ"=> Native.Chart.drive n
local notation "ν"=> direction ( «P»:=Site n ) ( G:=G )
local notation "Λ"=> Bare.Focus.Glow.e0 ( Position.glow G n )
local notation "Λₐ"=> Λe G n
local notation "Λς"=> Λc G n
local notation "αλ"=>alphabet G n
def palette (G:Gauge)(n:Side): Matrix (Position.Letter G n) (Full.Index G n) ℝ := (diagM (glyph (liftA G n)) (glyph (liftA G n)) (glyph (cLift G n)) 0).transpose.submatrix id (Full.alphabet G n).symm
lemma at_palette (i:L)(j:Based.Letters J C): palette G n i (αλ j)= diagM (glyph η) (glyph η) (glyph Ω) 0 j i:= by simp only [palette,Matrix.submatrix_apply,id_eq,Equiv.symm_apply_apply,Matrix.transpose_apply ]
lemma actually_real : Uₐ=(palette G n).map ((↑): ℝ→ℂ):= by ext i j:1; obtain ⟨j,rfl⟩:= ( Full.alphabet G n ).surjective j; rw [at_Ux,Matrix.map_apply,at_palette]; rcases i with (i|i)|(i|i)<;> rcases j with (j|j)|(j|j)<;> rfl
lemma counting {A:Type} [AddCommMonoid A](f:(Letters J C)→A): (∑ i,f i)=(∑ i,f (Based.a i))+(∑ i,f (Based.c i))+((∑ i,f (Based.k i))+(∑ i,f (Based.b i))):= by rw [Fintype.sum_sum_type]; simp [Fintype.sum_sum_type]
lemma tint (i:L): η (Λ i)=∑ j:V,palette G n i j • ν j:= by
    rw [← Equiv.sum_comp (Full.alphabet G n) (fun j:V=> palette G n i j • ν j), counting]; simp_rw [at_palette]; -- select legs
    simp only [ alph_a,alph_c,alph_k,alph_b,Full.select_a, Full.select_c, Full.select_k, Full.select_b,smul_zero, Finset.sum_const_zero,add_zero ]; rcases i with (i|i)|(i|i)<;> first| exact ( Native.frame _ ).symm | (change η 0=∑ i:J,(0:ℝ) • priv i; rw [map_zero]; simp) -- eta ambiguous parentheses
lemma pigment {A:T→ℝ} (h:germ A): pull Uₐ (ink ν A)= ink Λ (A ∘ η):= by
    let V' := (liftA G n).toContinuousLinearMap
    rw [ actually_real, pull_ink (palette G n) ν (V' ∘ Λ) _ h tint ]; exact Eq.symm ( ink_ctrl_one Λ V' h )
-- pair interleave over *all* positive links. Need true even for Φν Haar/log.
private def halves (he:Even n.val): OEdge n × Bool ≃ Edge (Site n):= by
    refine {
       toFun i:= if i.2 then i.1.val else Orb.reflect i.1.val
       invFun x:= (index x, decide (eR x=x))
       left_inv := ?_
       right_inv := ?_ }
    · rintro ⟨e,t⟩; have hx: eR e.val=e.val:= e.property; have hq : eR (Orb.reflect e.val)≠Orb.reflect e.val:= by rw [eR_reflect,hx]; exact Ne.symm (no_fixed_edge he _); -- guard
      have hv : index e.val=e:= Subtype.ext hx
      have hp : index (Orb.reflect e.val)=e:= Subtype.ext ((eR_reflect _).trans hx)
      cases t <;> simp [hx,-eR_reflect,hq,hv,hp]
    intro x; by_cases hv:eR x=x; · simpa [hv] using (show (index x).val=x from hv) -- progress
    simp only [ decide_eq_true_eq,hv,if_false ]; rw [ show (index x).val=Orb.reflect x from (eR_spec x).resolve_left hv ]; exact Orb.reflect_reflect _
lemma sum_halves {M:Type}[AddCommMonoid M] (he:Even n.val)(X:Edge (Site n)→ M) : ∑ i,X i= ∑ i:OEdge n,(X i.val+ X (Orb.reflect i.val)) := by rw [ ← Equiv.sum_comp (halves he) X, Fintype.sum_prod_type ]; simp only [halves]; simp -- test
lemma haar_full (he:Even n.val) : ( Native.Chart.totalH ∘ η ) =ᶠ[𝓝 0] (2:ℝ) • Position.logHaar := by
    filter_upwards [eventually_all.mpr fun i:OEdge n=> (show ∀ᶠ A:P in 𝓝 0, Maurer.lac (- (A i))= Maurer.lac (A i) from (continuous_apply i|>.tendsto (0:P)).eventually Maurer.opposite)] with A h
    simp_rw [Function.comp_apply, Pi.smul_apply,Position.logHaar, Native.Chart.totalH, sum_halves he ( X:=fun i=> Maurer.lac (η A i) ), Position.edge_even he, Position.edge_rep, h, Finset.sum_add_distrib ]; exact (two_smul ℝ _).symm

-- Ghost drift. all projection later requires this difference be on ad.
variable {T': Type}
def adF (g:G.Color) : (T'→G.Color)→ₗ[ℝ](T'→G.Color) := LinearMap.pi fun i => ( G.ad g ).comp (LinearMap.proj i)
lemma global_shift (u:G.Color): ∀ᶠ y:G.Color in 𝓝 0,Maurer.volts (u,u) y= - G.ad u y:= by
   obtain ⟨r,hr,W⟩:= LocalH.geom_patch G; let A:= W r le_rfl; filter_upwards [ Metric.ball_mem_nhds 0 hr ] with y hy
   let Vp:= fun t:ℝ=> G.lieExp (t • (-u)); have ht (x:ℝ): Maurer.step (u,u) y x=Vp x*G.lieExp y*(Vp x)⁻¹:= by unfold Vp Maurer.step; simp [Next.SectorChange.exp_negative]
   have hh := Maurer.amp (u,u) A hy; rw [ funext (show ∀ t:ℝ,G.plog ( G.mat (Maurer.step (u,u) y t))= G.adjoint (Vp t) y from fun t=> by rw [ht,← Maurer.runby]; exact Maurer.snap_on A (show G.adjoint (Vp t) y∈ Metric.ball 0 r from (by simpa using hy))) ] at hh; rw [hh.unique (Extra.WeakScaling.Color.tangent (-u) y), map_neg,LinearMap.neg_apply]
lemma ad_lifts (u:G.Color)(F:P) : adF u (η F) = η (adF u F):= by
    funext i; change G.ad u (edgeField n _ F i)=edgeField n _ _ _; rw [edge_spec,edge_spec]; split_ifs; · rfl
    rw [map_neg]; rfl
private lemma difference_volt (u:G.Color) : ∀ᶠ f:T in 𝓝 0, Native.Chart.roam χ f (remaining G n u)= - adF u f := by
    filter_upwards [eventually_all.mpr (fun i:Edge (Site n)=> (show ∀ᶠ f:T in 𝓝 0, Maurer.volts (u,u) (f i)= - G.ad u (f i) from (continuous_apply i|>.tendsto (0:T)).eventually (global_shift u)))] with f h; exact funext h
-- for based equivariant fields lifted to ambient, all orders
lemma roam_equiv (he:Even n.val)(u:Position.U G n): ∀ᶠ f:P in 𝓝 0, Native.Chart.roam χ (η f) (liftC G n u)= η (based f u) := by
   let Cg:= liftC G n u; let k (e: Edge (Site n)):= Native.Chart.route χ e Cg
   obtain ⟨r,hr,W⟩:= LocalH.geom_patch G; filter_upwards [ eventually_all.mpr (fun i:OEdge n=> (show ∀ᶠ f:P in 𝓝 0,f i∈Metric.ball 0 r from (continuous_apply i|>.tendsto (0:P)).eventually (Metric.ball_mem_nhds _ hr))) ] with f h
   have hh (e:OEdge n): η (based f u) e.val=Maurer.volts ( k e.val ) (f e):= by rw [liftA,edge_rep]; rfl
   have hr' (i:Site n): Cg (-i)=Cg i:= site_even u i
   have hk (e:Edge (Site n)) : k (Orb.reflect e)=(k e).swap:= by change (Cg (-e.1-step e.2), Cg (-e.1-step e.2+step e.2))= (Cg (e.1+step e.2),Cg e.1); rw [sub_add_cancel,hr', show -e.1-step e.2= -(e.1+step e.2) from (by abel),hr']
   refine funext (fun i=>?_); change Maurer.volts (k i) (η f i)=_; rcases (halves he).surjective i with ⟨⟨a,t⟩,rfl⟩; cases t
   · change Maurer.volts ( k (Orb.reflect a.val) ) (η f (Orb.reflect a.val))=η (based f u) (Orb.reflect a.val); simp_rw [liftA, edge_even he, hk,edge_rep]; rw [Maurer.comeback_field (k a.val) (W r le_rfl) ( h a ) ]; rfl
   change Maurer.volts (k a.val) (edgeField n _ f a.val)=_; rw [edge_rep]; exact (hh _).symm

def offsetGhost (i:GC): G.Color:= takeMean G n ( liftC G n (priv i) )
def flow (i:GC)(X:P): P := generator i X+ adF (offsetGhost i) X
lemma drift_priced (i:GC) : germ (flow i) := (ongoing i).add ( (adF (offsetGhost i) (T':=OEdge n)).toContinuousLinearMap.contDiff.contDiffAt )
lemma painted_flow (he:Even n.val)(i:GC): ∀ᶠ f:P in 𝓝 0, Native.Chart.roam χ (η f) (Ω (priv i))= η ( flow i f ) := by
    have ht : Tendsto η (𝓝 0) (𝓝 0):= by simpa using ( liftA G n|>.continuous_of_finiteDimensional ).tendsto (0:P)
    filter_upwards [ roam_equiv he (priv i), ht.eventually ( difference_volt ( offsetGhost i ) ) ] with f h hx;
    rw [show Ω (priv i)= liftC G n (priv i)- remaining G n (offsetGhost i) from rfl, map_sub,h,hx,flow,ad_lifts,map_add,sub_neg_eq_add ]; rfl
end YM.WilsonBridge.Injections
