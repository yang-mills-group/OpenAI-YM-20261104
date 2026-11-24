import YM.SchemeRG11.Saddle.Tide
/-! Slicing gauges — sets of local differential equations determining the Jacobian. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.SchemeRG11.Sway
open scoped Classical ContDiff Topology Matrix.Norms.Frobenius
open Function Filter Lattice Pert.Orb PertExtension.Orb LocalH MeasureTheory Precision Push.Loops
variable {G:Gauge}{n:Side}
private lemma rootwise(l : Site n→ G.Color→L[ℝ]G.Color)(h: ∀ x, l (-x)=l x): ∃ u: Parameter G n→L[ℝ] Parameter G n, ∀ v:Parameter G n,∀ x:Site n,(u v).val x=l x (v.val x):=by
 let t:= ray l
 let L:=t.toLinearMap.comp (Pert.Orb.Zero G n).subtype
 have hv(v:Parameter G n): L v ∈ Pert.Orb.Zero G n:=by
    refine ⟨fun x=>?_,?_⟩
    · change l (-x) (v.val (-x))= l x (v.val x); rw [h,(show _ ∧ _ from v.property).1 x]
    change l 0 (v.val 0)=0; rw [atZ v,map_zero]
 let u: Parameter G n →ₗ[ℝ] Parameter G n:= LinearMap.codRestrict (Pert.Orb.Zero G n) L hv
 exact ⟨u.toContinuousLinearMap,fun v x=>rfl⟩
private lemma root_norm(l : Site n→ G.Color→L[ℝ]G.Color)(u:Parameter G n→L[ℝ]Parameter G n)(hu: ∀ v:Parameter G n,∀ x:Site n,(u v).val x=l x (v.val x))(h:∀ a x,‖l a x‖=‖x‖):cost u=1:=by
 refine cost_norm _ fun a=>?_
 change ‖(u a).val‖=‖a.val‖; apply le_antisymm ((pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i=> ?_)) ((pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i=>?_))
 · rw [hu,h]; apply norm_le_pi_norm
 exact (by rw [← h i (a.val i), ← hu]; exact norm_le_pi_norm _ i)

def thrust(a:Parameter G n)(l:Site n):=G.lieExp (a.val l)
lemma thrust_inv(a:Parameter G n)(l:Site n): thrust a (-l)= thrust a l:=congrArg G.lieExp ((show _ ∧ _ from a.property).1 l)
lemma thrust_flat(a:Parameter G n):thrust a 0=1:=by unfold thrust;rw [atZ,G.mat_lieExp_zero]
private lemma hτ(s:Parameter G n)(x:Site n): theta (s.val (-x))= theta (s.val x):=congrArg theta ((show _ ∧ _ from s.property).1 x)
def stage(s:Parameter G n): Parameter G n→L[ℝ] Parameter G n:= Classical.choose (rootwise (fun i:Site n=>theta (s.val i)) (hτ s))
lemma stage_apply(s v:Parameter G n)(x:Site n):(stage s v).val x=theta (s.val x) (v.val x):=Classical.choose_spec (rootwise (fun i:Site n=>theta (s.val i)) (hτ s)) v x
private lemma hK(s:Parameter G n)(x:Site n): drift ((thrust s (-x))⁻¹)=drift ((thrust s x)⁻¹):=by rw [thrust_inv]
def undress(s:Parameter G n): Parameter G n→L[ℝ] Parameter G n:=Classical.choose (rootwise (fun i:Site n=>drift (thrust s i)⁻¹) (hK s))
lemma undress_apply(s v:Parameter G n)(x:Site n):(undress s v).val x=G.adjoint ((thrust s x)⁻¹) (v.val x):=Classical.choose_spec (rootwise (fun i:Site n=>drift (thrust s i)⁻¹) (hK s)) v x
lemma cost_undress(s:Parameter G n):cost (undress s)=1:=root_norm _ (undress s) (Classical.choose_spec (rootwise (fun i:Site n=>drift (thrust s i)⁻¹) (hK s))) (fun _ _=> G.norm_adjoint _ _)
def ravel(s:Parameter G n): Dir G n × Twig G n→L[ℝ] Dir G n × Twig G n:= ContinuousLinearMap.prodMap (ray (fun l:Cotree n=> drift ((thrust s l.val.val.1)⁻¹))) (ray (fun l:Trees n=> drift ((thrust s l.val.val.1)⁻¹)))
lemma cost_ravel(s:Parameter G n):cost (ravel s)=1:=by
 let A:=ray (fun l:Cotree n=>drift ((thrust s l.val.val.1)⁻¹)); let B:=ray (fun l:Trees n=>drift ((thrust s l.val.val.1)⁻¹))
 rw [cost_up _ A B (fun x=>by change (A x,B 0)=_; rw [map_zero]) (fun y=>rfl),cost_ray,cost_ray]; simp_rw [cost_drift]; simp

def stream(hn:Even n.val)(x:Whole G n): Whole G n→L[ℝ]Parameter G n:= (stage (swing G hn x)).comp (fderiv ℝ (swing G hn) x)
def vine(hn:Even n.val)(x:Whole G n): Whole G n→L[ℝ] Dir G n×Twig G n:= ravel (swing G hn x) ∘L road (graze hn x) ∘L ((twin hn).toContinuousLinearMap ∘L fderiv ℝ (graze (G:=G) hn) x)

lemma down_rate (hn:Even n.val):∀ᶠ x:Whole G n in 𝓝 0, let v:=graze hn x; let s:=swing G hn x
       let a:=branchL G hn x.1; let L:=fderiv ℝ (graze (G:=G) hn) x
       (∀ p:Whole G n, dLin (L p) = p.2) ∧
       ∀ p:Whole G n, let b:=branchL G hn p.1; let c:=stream hn x p
       ∀ l:Pert.Orb.Links n, theta (v.val l) ((L p).val l)= c.val l.1 + G.adjoint (thrust s l.1) (theta (a.val l) (b.val l)) -G.adjoint (positiveLinks v l) (c.val (l.1+step l.2)) :=by
 filter_upwards [(graze_smooth G hn).eventually (by simp), (swing_smooth G hn).eventually (by simp), eventually_eventually_nhds.mpr (graze_div G hn), eventually_eventually_nhds.mpr (graze_eq G hn)] with x hx hu hd hi
 intro v s a L
 have hxs: positiveLinks v = Lattice.gauge (thrust s) (positiveLinks a):=by rw [show positiveLinks a= _ from bark_pos hn x.1]; exact mem_of_mem_nhds (s:={x|positiveLinks (graze hn x)= Lattice.gauge (thrust (swing G hn x)) (representative x.1)}) hi
 let k:=graze (G:=G) hn; let B:= swing G hn; let M:Whole G n→L[ℝ] Potential G n:= branchL G hn ∘L ContinuousLinearMap.fst ℝ _ _
 constructor
 · let D:= dLin (G:=G) (n:=n) |>.toContinuousLinearMap; let J:=ContinuousLinearMap.snd ℝ (Dir G n) ↥(Flow G n)
   have hh:D ∘L L = J:= ((D.hasFDerivAt.comp x (hx.differentiableAt (by simp)).hasFDerivAt).congr_of_eventuallyEq (f₁:=J) (hd.mono fun i hi=>hi.symm)).unique J.hasFDerivAt
   exact fun p=>DFunLike.congr_fun hh p
 intro p b c l
 have hτ (y:Site n): Pulse (fun t=>thrust (B (rake x p t)) y) 0 (c.val y):=by
    let L:= (siteEval (G:=G) y).toContinuousLinearMap
    have h:= Pulse.draw (f:=L ∘ B) (x:=x) (L.contDiff.contDiffAt.comp x hu) p
    rw [fderiv_comp x L.differentiableAt (hu.differentiableAt (by simp)), L.fderiv] at h
    unfold c stream; simp only [ContinuousLinearMap.comp_apply]; rw [stage_apply]; exact h
 have heq : (fun t=> positiveLinks (k (rake x p t)) l) =ᶠ[𝓝 (0:ℝ)] fun t=> thrust (B (rake x p t)) l.1 * positiveLinks (M (rake x p t)) l * (thrust (B (rake x p t)) (l.1+step l.2))⁻¹:=by
    have hz:= (rake_rate x p).continuousAt.tendsto; rw [show rake x p 0=x by simp [rake]] at hz
    filter_upwards [hz.eventually hi] with i he
    have he: positiveLinks (k (rake x p i))= Lattice.gauge (thrust (B (rake x p i))) (representative (rake x p i).1):=he
    change positiveLinks (k (rake x p i)) l= _; rw [he, ← bark_pos hn _]; rfl
 have ht:= hτ l.1 |>.three (Pulse.links (f:=M) (x:=x) M.contDiff.contDiffAt p l) (hτ (l.1+step l.2))
 have h0: rake x p 0=x:=by simp [rake]
 rw [M.fderiv] at ht; rw [h0] at ht
 apply Pulse.unique ((Pulse.links hx p l).change heq); rw [hxs]; exact ht

lemma valve_rate (hn:Even n.val):∀ᶠ x:Whole G n in 𝓝 0,
    let U:= graze hn x
    let T:= swing G hn x
    let W:= vine hn x
    (∀ A, FPDeriv U (stream hn x ((0:Dir G n),A))=A) ∧
    ∀ p:Whole G n, let c:=stream hn x p
      (W p).2= stem hn (undress T c) ∧ (∀ l:Cotree n,
          (W p).1 l=submerge x.1 p.1 l+ (undress T c).val l.val.val.1 - G.adjoint (positiveLinks (branchL G hn x.1) l.val.val) ((undress T c).val (l.val.val.1+step l.val.val.2))) :=by
 have ht:Tendsto (graze (G:=G) hn) (𝓝 0) (𝓝 0):=Eq.subst (motive:=fun a=>Tendsto _ _ (𝓝 a)) (graze_flat G hn) (graze_smooth G hn).continuousAt.tendsto
 filter_upwards [down_rate (G:=G) hn, ht.eventually (entry_rate), ht.eventually theta_nz, graze_eq G hn] with x hu hv hθ ht
 intro U T W
 let L:= fderiv ℝ (graze (G:=G) hn) x
 change (∀ p:Whole G n,dLin (L p)=p.2) ∧ _ at hu
 constructor
 · intro A; let p:Whole G n:=(0,A); let c:=stream hn x p
   rw [←(hv c).1]; change dLin (atVertical U c)=_
   have he: L p= atVertical U c:= Subtype.ext (funext fun i=> hθ i (by
      have hh:= hu.2 p i; simp only [p,map_zero,Submodule.coe_zero,Pi.zero_apply,add_zero] at hh; exact hh.trans (hv c|>.2 i).symm))
   rw [← he]; exact hu.1 p
 intro p c
 let f:=undress T c; let s:=thrust T; let k:=branchL G hn
 let Q:= positiveLinks (k x.1)
 have hw(i:Pert.Orb.Links n): G.adjoint (s i.1)⁻¹ (theta (U.val i) ((L p).val i))= f.val i.1 + theta ((k x.1).val i) ((k p.1).val i) - G.adjoint (Q i) (f.val (i.1+step i.2)):=by
    rw [hu.2 p i]; change G.adjoint _ (c.val _ + G.adjoint (s i.1) _ - G.adjoint (positiveLinks U i) _)= _
    have he : positiveLinks U= Lattice.gauge s (positiveLinks (k x.1)):=by rw [bark_pos hn x.1];exact ht
    rw [map_sub,map_add,← G.adjoint_mul,inv_mul_cancel,G.adjoint_one,← G.adjoint_mul (s i.1)⁻¹,he,show (s i.1)⁻¹*Lattice.gauge s (positiveLinks (k x.1)) i=Q i*(s (i.1+step i.2))⁻¹ by unfold Q Lattice.gauge; group,G.adjoint_mul (Q i)]
    unfold f; rw [undress_apply,undress_apply]
 constructor
 · ext1 i; change G.adjoint (s i.val.val.1)⁻¹ (theta (U.val i.val.val) ((L p).val i.val.val)) = struts f i
   rw [hw i.val.val]; have hj(t:Dir G n): (k t).val i.val.val=0:=by rw [show (k t).val = variation t from twin_twists hn t];exact variation_branch t i
   unfold Q; rw [hj,hj, positiveLinks,hj,G.mat_lieExp_zero,map_zero,G.adjoint_one,add_zero]; rfl
 intro i
 change G.adjoint (s i.val.val.1)⁻¹ (theta (U.val i.val.val) ((L p).val i.val.val)) = _; rw [hw i.val.val]; have hj(t:Dir G n): (k t).val i.val.val=t i:=by rw [show (k t).val = variation t from twin_twists hn t];exact variation_others t i
 rw [hj,hj,add_comm]; rfl
end YM.SchemeRG11.Sway
