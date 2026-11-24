import YM.RegulatorIR.Axial.Values

/-!
# Actual patch for local W1 vacuum on the cover
Lift the compact star of every site with needed gauge pulse.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Axial
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight PowerSeries Gain Prim Motion Budget.Packet Budget.Deck Finset
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries
variable {f:Side}{G:Gauge}

lemma step_one (x:Edge Cover) (z:Side) : secure 1 f z x=around (rep f z) (deep f z x):=by unfold secure entering centreE; rw [Signed.act_one];rfl
lemma trackzero (t:ℝ) : crest (0:Trip G) t=0:=by
 by_cases ht:t=0
 · subst t; simp [crest_origin]
 apply (smul_right_injective (G.Color) ht); dsimp only; rw [smul_zero,crest_v,smul_zero,bill_z]
variable (A:BEdge G)(σ:Cover→ G.Color)(h:4≤ f.val)(hp:Even f.val)

lemma usesT (z:Side){i}(H:track z h A i≠0): ∃ j:Edge Cover,A j≠0 ∧ sig 1 f z j=i:=by
 by_cases hx:i∈Set.range (slotE z h)
 · obtain ⟨j,hj⟩:=hx
   refine ⟨j.val,fun h'=>H ?_,?_⟩
   · unfold track;rw [← hj, Function.Injective.extend_apply (slotE z h).injective]; unfold Gain.camp; split <;> simp [h']
   rw [sig, step_one]; exact hj
 exact (H (Function.extend_apply' _ _ _ hx)).elim
lemma usesS (z:Side){i:Site (rep f z)}(H:dropV z h σ i≠0): ∃ j:Cover,σ j≠0∧(i=swim f z j ∨ i= -swim f z j):=by
 by_cases hx:vertex i ∈ Set.range (slotS z h)
 · obtain ⟨j,hj⟩:=hx
   refine ⟨j.val,fun h'=>H ?_,?_⟩
   · unfold dropV; rw [← hj, Function.Injective.extend_apply (slotS z h).injective,h']
   let x:=swim f z j.val; change vertex x=vertex i at hj
   rcases vertex_spec x with h|h <;> rcases vertex_spec i with ht|ht <;> rw [h,ht] at hj
   · exact Or.inl hj.symm
   · right; unfold x at hj; rw [hj,neg_neg]
   · exact Or.inr hj.symm
   exact Or.inl (neg_inj.mp hj).symm
 exact (H (Function.extend_apply' _ _ _ hx)).elim

-- expose lifts in a local stars frame
abbrev behind {z:Side}(S: Finset (Edge Cover))(v: OEdge (rep f z)) -- z implicit
 : Prop:=∃ i∈ S,sig 1 f z i=v
variable (S:Finset (Edge Cover))(hA:Function.support A⊆(↑S:Set _))
variable (hL:∀ x, x∈ Function.support σ → ∀ v:Axis,(x,v)∈S)
variable (hR:∀ x, x∈ Function.support σ → ∀ v:Axis,(x-step v,v)∈S)
include hA
lemma track_here (z:Side)(u:OEdge (rep f z))(H:track z h A u ≠0) : behind S u (f:=f) (z:=z):=by
 obtain ⟨i,hi,ht⟩:= usesT A h z H; exact ⟨i,hA hi,ht⟩
omit hA
include hL hR
omit hL hR in
lemma base_step (x:Cover)(z:Side)(v:Axis): swim f z (x+step v)=swim f z x+step v:=by unfold swim; rw [← add_assoc,map_add,wrap_step]
lemma flash_at (z:Side)(u:OEdge (rep f z)) (H : dropV z h σ u.val.1≠0 ∨ dropV z h σ (u.val.1+step u.val.2)≠0) : behind S u (f:=f) (z:=z):=by
 let t:=u.val; let d:= t.2; let a:=t.1; let k:=swim f z
 have he(x:Cover): k (x-step d)=k x-step d:=by
    apply eq_sub_of_add_eq; rw [← base_step]; simp; rfl
 have hx (x:Cover)(hr:k x=a) : sig 1 f z (x,d)=u:=by rw [sig,step_one, show around _ (deep f z (x,d))=(a,d) from Prod.ext hr rfl]; exact Subtype.ext u.property
 have hp (x:Cover)(hr:k x= -a-step d) : sig 1 f z (x,d)=u:=by
   rw [sig,step_one,show around _ (deep f z (x,d))= reflect t from Prod.ext hr rfl]; exact Subtype.ext ((eR_reflect t).trans u.property)
 rcases H with H|H
 · obtain ⟨i,hi,h'|h'⟩:= usesS σ h z H
   · exact ⟨(i,d),hL _ hi _,hx _ h'.symm⟩
   refine ⟨(i-step d,d),hR _ hi _,hp _ ?_⟩; rw [he,show a= -k i from h',neg_neg]
 obtain ⟨i,hi,h'|h'⟩:= usesS σ h z H
 · refine ⟨(i-step d,d),hR _ hi _,hx _ ?_⟩; rw [he,show k i= a+step d from h'.symm,add_sub_cancel_right]
 refine ⟨(i,d),hL _ hi _,hp _ ?_⟩; rw [show -a-step d= -(a+step d) by abel,show _+_= -k i from h',neg_neg]
include hA
lemma winged (z:Side)(u:OEdge (rep f z))(t:ℝ)(hi:eyes A σ h z t u≠0): behind S u (f:=f) (z:=z):=by
 by_cases he: track z h A u=0
 · apply flash_at σ h S hL hR z u
   by_contra! hb
   exact hi (by change crest _ t=_; rw [show violetO (track z h A) (dropV z h σ) u=0 from Prod.ext he (Prod.ext hb.1 hb.2),trackzero])
 exact track_here A h S hA z u he
lemma radius (u:Edge Cover)(t:ℝ)(hz:u∉ S) : crest (violet A σ u) t=0:=by rw [show violet A σ u=0 from ?_,trackzero]; refine Prod.ext (Function.notMem_support.mp (fun h=>hz (hA h))) (Prod.ext (Function.notMem_support.mp (fun h=>hz (hL _ h u.2))) (Function.notMem_support.mp (fun h=>hz ?_))); simpa using hR _ h u.2
omit hR hA hL
lemma receipt {p:Signed}{X:(z:Side)→ℝ→Horizon G (rep f z)}(z)(h:∀ t u,X z t u≠0 → ∃ i∈S,sig p f z i=u): Function.support (vow (peel (X z)))⊆ Set.range (fun i: medal S G=> (sig p f z (wire S i).1,(wire S i).2)):=by
 intro a ha
 by_cases hx:∃ t,X z t a.1≠0
 · obtain ⟨t,hx⟩:=hx; obtain ⟨x,h₁,h₂⟩:= h _ _ hx; exact ⟨(⟨x,h₁⟩,a.2), Prod.ext h₂ rfl⟩
 push Not at hx;apply (ha _).elim; change tale (fun t=>(X z t a.1) a.2)= _; simp_rw [hx,PiLp.zero_apply,tale_const,map_zero]
include hA

def scriptT : Brief 1 f (fields A h) (vow (fun _=>hue A)):= {
 stampK:= S, suited:= by
    intro x hx; refine ⟨(⟨x.1,hA (fun h=>hx ?_)⟩,x.2),rfl⟩;change tale (fun _=> A x.1 x.2)=0; rw [h]; simp [tale_const]
 sky:= Eventually.of_forall fun _=>contDiffAt_const, endQ:= Eventually.of_forall fun z=> receipt S z (fun _=> track_here A h S hA z), pays:=by
    refine eventually_all.mpr fun i=>?_
    let j:= wire S i; filter_upwards [included j.1.1] with z hz; change tale (fun t=>fire (track z h A) _ _)=tale (fun _=> A j.1 j.2); simp_rw [step_one]; apply congr_arg; ext1; rw [track_link z h A j.1 hz] }
include hL hR hp

def scriptK : Brief 1 f (eyes A σ h) (vow (shadowU A σ)):= {
 stampK:= S, suited:= by
   intro x hx; have hh: x.1∈ S:=by
       by_contra! he; apply hx; change tale (fun t=> crest _ _ _)=0; simp_rw [fun t=>radius A σ S hA hL hR x.1 t he,PiLp.zero_apply,tale_const,map_zero]
   exact ⟨(⟨x.1,hh⟩,x.2),rfl⟩
 sky:= Eventually.of_forall (fun z=> current_space _ _), endQ:= Eventually.of_forall fun z=>receipt S z (fun t x hx=> winged A σ h S hA hL hR z x t hx), pays:=by
   refine eventually_all.mpr fun i=>?_
   let x:Foot G:= wire S i; filter_upwards [included x.1.1,included (x.1.1+step x.1.2)] with z hx hp';change tale (fun t:ℝ=>fire _ (secure _ _ z x.1) _)= _
   unfold vow; simp_rw [step_one]; refine tale_eq ?_ (eyes_up A σ h hp z x.1 hx hp' x.2)
   let P:G.Color→L[ℝ] ℝ:=PiLp.proj 2 _ x.2; exact P.contDiff.contDiffAt.comp _ (crest_smooth _) }
end YM.RegulatorIR.Axial
