import YM.RGComparison.Core16.Lam.Coat
/-!
# Genuine plane capitalization (log derivative at Θ chart center by primitive seam local moments)

No neglecting literature normalization. Unmarked log **action** not NegStep.patch complexity by valve expansion.
Beta=g⁻² here AFTER incoming estimates. f.TopSeam normalization Maker collects all V.
This script realizes derivative `first` as path Pinage.Mat.VW projector (actually score cross at second order), Ray moments including Θ labels with attributes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lam
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity Finset
open Precision Push.BetaTransport Next.Fluctuations Pressure
open scoped Topology ContDiff BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{S:Side}{ι :Type}[Fintype ι]
variable {c f: Side} (S : StepData c f) (T:Forest S.ratio)(t:S.Choices)
-- bookkeeping sum-integrable lemmas needed throughout.
variable (h:S.patch.Branches S.kernel G)
set_option quotPrecheck false
local notation "μ"=> skillet G T.Free
include h

-- normalized relative constant
lemma smooth_steps (g:ℝ): ContDiff ℝ ∞ (collects (G:=G) S T g) := ContDiff.sum (s:=univ) (f:=fun t (u:Directions G c)=>∫ x, bonnet S T t g u x∂skillet G T.Free) fun t _=> by obtain ⟨K,hK,hp,hF⟩:= huts S T t h; exact pole_hot hF.aestronglyMeasurable hK hp (flavor S g)
lemma positive (g:ℝ) (u:Directions G c):0<collects S T g u:= by
    rw [collects,←integral_finsetSum univ]; swap ; exact fun t _=> by obtain ⟨K,hK,hp,hF⟩:= huts S T t h; exact addition hF.aestronglyMeasurable hK hp (flavor _ g) u
    let V:=stature u; let Φ: Sky G T.Free→ℝ:= fun x=> ∑ t, bonnet S T t g u x; have hΦ: Integrable Φ μ:= integrable_finsetSum _ fun i hi=> by obtain ⟨K,hK,hp,hF⟩:= huts S T i h; exact addition hF.aestronglyMeasurable hK hp (flavor _ g) u
    have Hp(x:Sky G T.Free):0<Φ x:=by
        unfold Φ; simp_rw [leaflet]; obtain ⟨t,hv,hV⟩:= (sum_pos_iff_of_nonneg (f:=S.likelihood (T.drape x)) (fun i _ => S.likelihood_pos ..)).1 ((S.chosen h (T.drape x)).symm ▸ zero_lt_one)
        exact Finset.sum_pos' (fun i _=>mul_nonneg (S.likelihood_pos ..) (Base.cash_pos ..|>.le)) ⟨t,hv,mul_pos hV (Base.cash_pos ..)⟩
    apply (integral_pos_iff_support_of_nonneg (fun i=> (Hp i).le) hΦ).2; rw [show Function.support Φ=Set.univ from Set.eq_univ_of_forall (fun i=> (Hp i).ne')]; simp

local notation "Y"=> Directions G c

def raise (S:StepData c f)(u:Y)(w:News G c):= line1 (tax S w) 0 u

def tip (S:StepData c f)(u v:Y)(w:News G c):= lend (tax S w) u v
omit h
lemma raise_hot (u:Y): ContDiff ℝ ∞ (raise S u) := by
    let F : Directions G c× News G c→ℝ:=fun u=>tax S u.2 u.1
    exact (ContinuousLinearMap.apply ℝ ℝ u).contDiff.comp ((stem_hot (tax_hot (G:=G) S|>.of_le le_top)).comp (f:=fun y=>(0,y)) (contDiff_const.prodMk contDiff_id))
lemma tip_hot (u v:Y): ContDiff ℝ ∞ (tip S u v)  := by
    let A:=(ContinuousLinearMap.apply ℝ ℝ v).comp (ContinuousLinearMap.apply ℝ (Directions G c→L[ℝ] ℝ) u)
    exact A.contDiff.comp ((stem_hot (stem_hot (tax_hot (G:=G) S|>.of_le le_top))).comp (f:=fun y=>(0,y)) (contDiff_const.prodMk contDiff_id))

def turn (g:ℝ)(F: News G c→ℝ) := ∑ t,reel S T t g F
abbrev port (g:ℝ)(F:News G c→ℝ):= turn S T g F / collects (G:=G) S T g 0

variable {F F':News G c→ℝ} (hF:ContDiff ℝ ∞ F)(hF':ContDiff ℝ ∞ F')
include h hF in
lemma at_helm (g:ℝ) : Integrable (fun x=>leaf S g (fire S T t x) 0 * F (fire S T t x)) μ:=by
     obtain ⟨K,hK,hp,h₁⟩:= huts S T t h; refine addition h₁.aestronglyMeasurable hK hp (ContDiff.mul (flavor _ g) (hF.comp contDiff_snd)) (0:Y)

include h
include hF hF' in
lemma stack (g:ℝ) : turn S T g (F+F') = turn S T g F+turn S T g F':=by
    have hf (t:S.Choices):= integral_add (at_helm S T t h hF g) (at_helm S T t h hF' g)
    unfold turn reel; simp_rw [Pi.add_apply,mul_add,hf]; rw [sum_add_distrib]

omit h in
lemma tack (g:ℝ)(F:News G c→ℝ)(r:ℝ): turn S T g (r • F)= r*turn S T g F:= by unfold turn reel; simp_rw [Pi.smul_apply,smul_eq_mul,mul_left_comm _ r,integral_const_mul,←mul_sum]

omit h in
private lemma leafy (p:News G c)(u v: Directions G c)(g:ℝ):
     let C:= leaf S g p; let A:= -(g⁻¹^2); let F:= A • raise S u; let D:= A^2 • (raise S u * raise S v)+ A • tip S u v
     line1 C 0 u=C 0* F p ∧ lend C u v=C 0* D p:=by
    intro C A F D; let W:=tax S p; have h: ContDiff ℝ ∞ W:= ((tax_hot S).of_le le_top).comp (f:=fun x: Directions G c =>(x,p)) (contDiff_id.prodMk contDiff_const)
    let V:=Real.exp ∘(A • W); have hf:ContDiff ℝ ∞ V:= (h.const_smul A).exp
    obtain ⟨hy,hv⟩:= earnings h u v A; obtain ⟨hp,hT⟩:=faculty hf u v p.1; change line1 (p.1 • V) _ _= p.1 * V 0 *(A*line1 W 0 u) ∧ lend (p.1 • V) u v = p.1* V 0*(A^2*(line1 W 0 u* line1 W 0 v)+A* lend W u v); change line1 V 0 u= _ at hy; change lend V _ _= _ at hv; rw [hp,hT,hv,hy]; unfold V; constructor <;> ring

omit h in
private lemma sigma {L:Type*}[NormedAddCommGroup L][NormedSpace ℝ L](f:ι→ L→ℝ) (h:∀ i,ContDiff ℝ ∞ (f i))(u v:L) :
    let C:= fun x=>∑ i,f i x; line1 C 0 u=∑ i,line1 (f i) 0 u ∧ lend C u v=∑ i, lend (f i) u v:=by
    intro C; unfold line1 lend Hess; rw [show fderiv ℝ C= ∑ i,fderiv ℝ (f i) from (funext fun i=> (HasFDerivAt.fun_sum (u:=univ) fun a _=>(Diff (h a) i).hasFDerivAt).fderiv.trans (Finset.sum_apply ..).symm), (HasFDerivAt.sum (x:=0) (u:=univ) fun a _=>(wander (h a) 0).hasFDerivAt).fderiv]; simp_rw [Finset.sum_apply,_root_.sum_apply]; simp -- drop h include

lemma quotes (g:ℝ) (u v: Y) :
   let W:=collects (G:=G) S T g; let k:= -(g⁻¹^2)
   line1 W 0 u = k*turn S T g (raise S u) ∧ lend W u v=k^2 * turn S T g (raise S u * raise S v) + k*turn S T g (tip S u v):=by
   intro W k; let Φ := fun (w:Y × News G c)=> leaf S g w.2 w.1; let p := fire (G:=G) S T; let Z(i:S.Choices):= pole (u:=skillet G T.Free) (p i) Φ; have ht : W=fun x=>∑ a,Z a x:=rfl
   have hk i:= (huts S T i h); choose K hK h₁ h₂ using hk
   have hZ i: ContDiff ℝ ∞ (Z i):= pole_hot (h₂ i).aestronglyMeasurable (hK i) (h₁ i) (flavor _ g); obtain ⟨hf,he⟩:= sigma Z hZ u v -- include h?
   rw [ht,hf,he]; let U:=k^2 • (raise S u*raise S v); let V:= k • tip S u v; constructor
   · rw [← tack S T]; refine sum_congr rfl (fun i _=>?_); unfold Z; rw [slope_rule (h₂ i).aestronglyMeasurable (hK i) (h₁ i) (flavor _ g)]; exact integral_congr_ae (Eventually.of_forall fun x=> (leafy _ (p i x) u v g).1)
   rw [← tack S T,← tack S T, ← stack S T h (show ContDiff ℝ ∞ U from ((raise_hot S u).mul (raise_hot S v)|>.const_smul (k^2))) (F':= k • tip S u v) ((tip_hot S u v).const_smul k)]; apply sum_congr rfl (fun i _=>?_); unfold Z; rw [exactL (h₂ i).aestronglyMeasurable (hK i) (h₁ i) (flavor _ g)]; exact integral_congr_ae (Eventually.of_forall fun x=> (leafy _ (p i x) u v g).2)

-- actual PT orientation at all degrees. Use `probe` impulses 🌈 anchor

def centered (S:StepData c f)(g:ℝ)(u: Y): ℝ:= -Real.log (S.push (g⁻¹^2) (bare (g⁻¹^2)) (stature u))

def measure (S:StepData c f)(g:ℝ)(u v:Y): ℝ:= g^2*lend (centered S g) u v

lemma measure_point {g:ℝ}(hx:g≠0)(u v:Y): measure S g u v= port S T g (tip S u v) - (port S T g (raise S u*raise S v)- port S T g (raise S u)*port S T g (raise S v))/g^2:= by
   let p:= Next.Fluctuations.Sector.prefactor S G (g⁻¹^2); have hz:0<p:= pow_pos (inv_pos.mpr (S.penaltyZ_pos _)) _
   let W:=collects (G:=G) S T g; let K:=p • W; have hp:= smooth_steps S T h g; have ht : ContDiff ℝ ∞ K := hp.const_smul p; have he: ∀ x,0<W x:= fun x=>positive S T h g x
   have hK:centered S g= fun x=> -Real.log (K x) := by funext u; rw [centered,income S T h]; rfl
   unfold measure; rw [hK,logH ht (show 0<K 0 from mul_pos hz (he _)),show Lam.line1 K .. = _ from (faculty hp u v p).1,show Lam.line1 K .. = _ from (faculty hp v u p).1, show lend K .. = _ from (faculty hp u v p).2,(quotes S T h g u v).1,(quotes S T h g v u).1,(quotes S T h g u v).2]; unfold port; change g^2* (_ / (p*W 0)^2-_/(p*W 0)) = _/W 0-(_/W 0-_/W 0* (_/W 0))/ _; have hh:= (he 0).ne'; field_simp; ring
end YM.RGComparison.Core16.Lam
