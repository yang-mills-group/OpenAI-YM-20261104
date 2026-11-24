import YM.RegulatorIR.Ward.Eddy

/-!
# Signed axis group on the *working* inversion quotient
Be careful: even with patch choices obeying all requirements the off-branch
frozen extension we used need not commute. Prove this property only as a germ
at each pure gauge.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Axial
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Chart RG Laplace Binding Ward
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius
variable {c f : Side}{G:Gauge}
variable (p: YM.Signed) (U V:spins G f)(he:Even f.val)

abbrev sent (p:Signed)(x: Edge (Site f)):= sendEdge p 0 x
def blink (p:Signed)(x:Edge (Site f)) : Bool:= ((posDir x.2).rotate p).neg
lemma look (x:Edge (Site f)) (V:Config G f): pull p 0 V x=if blink p x then (V (sent p x))⁻¹ else V (sent p x):= rfl
lemma sent_there (x: Edge (Site f)): sent p (reflect x)=reflect (sent p x):=by
 rcases x with ⟨y,i⟩; let d:= (posDir i).rotate p
 have hx: p.act (step i:Site f)=d.vec:=(by rw [← Step.vec_pos i]; exact Eq.symm (Step.vec_rotate ..)) -- fix
 change d.used (p.act (-y-step i)+0)=reflect (d.used (p.act y+0))
 rw [p.act_sub, p.act_neg,add_zero,add_zero,hx]
 rcases d with ⟨a,h|h⟩
 · rfl
 simp only [Step.used,Step.vec,↓reduceIte,reflect]; congr 1; congr 1; abel

include he
lemma orbit_p (x:Edge (Site f)) : pull p 0 (orbLift U) (reflect x)= (pull p 0 (orbLift U) x)⁻¹:=by
 rw [look,look,sent_there,show blink p (reflect x)=blink p x from rfl, show orbLift U _= (orbLift U _)⁻¹ from lift_flip he ..]; split <;> rfl
def cane (p:Signed)(U:spins G f):spins G f:= fun x=>pull p 0 (orbLift U) x.val
lemma lifted : orbLift (cane p U)=pull p 0 (orbLift U):=by
 obtain ⟨W,h⟩:= is_sheet (pull p 0 (orbLift U)) (orbit_p p U he); suffices hh:cane p U=W by rw [hh,←h]
 ext1 i; unfold cane;rw [h]; exact lift_at ..
lemma spins_bij : cane p⁻¹ (cane p U)=U:=by
 ext1 i; unfold cane; change pull p⁻¹ 0 (orbLift (cane p U)) _=_; rw [lifted p U he,pull_pull,mul_inv_cancel,affine,p.act_zero,add_zero,pull_id];exact lift_at ..

omit he
def route (p:Signed)(e:OEdge f): OEdge f:=index (sent p e.val)
lemma routed : Injective (route p (f:=f)):=by
 intro i j h;change index (sent p _)= _ at h
 have ht:eR (sent p i.val)=eR (sent p j.val):= congr_arg (·.val) h
 let F:=sent p (f:=f)
 rcases eR_spec (F i.val) with hx|hx <;> rcases eR_spec (F j.val) with hy|hy <;> rw [show eR (sent p i.val)= _ from hx,show eR (sent p j.val)= _ from hy] at ht
 · exact Subtype.ext (sendEdge_injective p _ ht)
 · have hz: i.val=reflect j.val:= sendEdge_injective p (0:Site f) (ht.trans (sent_there p _).symm)
   exact Subtype.ext (i.property.symm.trans ((congr_arg eR hz).trans ((eR_reflect _).trans j.property)))
 · have hz: reflect i.val=j.val:=sendEdge_injective p (0:Site f) ((sent_there p _).trans ht)
   exact Subtype.ext (i.property.symm.trans ((eR_reflect _).symm.trans ((congr_arg eR hz).trans j.property)))
 exact Subtype.ext (sendEdge_injective p (0:Site f) ((show Involutive (reflect (n:=f)) from fun _=>reflect_reflect ..).injective ht)) -- name
def swayE (p:Signed)(e:OEdge f)(x:G.El): G.El:=
 let j:=sent p e.val
 let s:= if eR j=j then x else x⁻¹
 if blink p e.val then s⁻¹ else s
lemma swings (e:OEdge f) : cane p U e=swayE p e (U (route p e)):= rfl
lemma swayed (e:OEdge f): MeasurePreserving (swayE (G:=G) p e) G.probHaar G.probHaar :=by
 unfold swayE; dsimp only; split_ifs <;> first| (simp only [inv_inv]; exact MeasurePreserving.id G.probHaar)|exact MeasurePreserving.id G.probHaar | exact G.preserve_inv
lemma measured : MeasurePreserving (cane (G:=G) p) (spinsMeasure G f) (spinsMeasure G f):=by
 let e:=Equiv.ofBijective _ ⟨routed p (f:=f),Finite.injective_iff_surjective.mp (routed p)⟩
 let fn(U: spins G f) (v:OEdge f):=U (route p v)
 have he : MeasurePreserving fn (spinsMeasure G f) (spinsMeasure G f):=by
    have ht:=measurePreserving_piCongrLeft (fun _:OEdge f=>G.probHaar) e.symm
    convert ht using 1 <;> first|rfl|skip
    funext k i; change k (e i)= _;simp [MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft_apply]
 let g(U:spins G f) (v:OEdge f):=swayE p v (U v)
 have hp:MeasurePreserving g (spinsMeasure G f) (spinsMeasure G f):=measurePreserving_pi _ _ (swayed p)
 exact hp.comp he

def caned (p:Signed)(he:Even f.val): spins G f≃ᵐ spins G f where
 toFun:=cane p
 invFun:=cane p⁻¹
 left_inv U:=spins_bij p U he
 right_inv U:=by simpa using spins_bij (p⁻¹) U he
 measurable_toFun:= (measured p).measurable
 measurable_invFun:= (measured p⁻¹).measurable

lemma compatible_beam {k:Site f → G.El}(h:compatible k): compatible (k ∘ p.act):=fun i=> (congr_arg k (p.act_neg i)).trans (h _)
lemma routed_gauges (k: Site f→ G.El)(h:compatible k) : cane p (goat k U) = goat (k ∘ p.act) (cane p U):=by
 ext1 i;rw [goat_at,cane,goat_lift k U h]
 unfold pull; rw [Step.gauge_read]; unfold affine; rw [Step.vec_rotate, Step.vec_pos,add_zero]; change _=k (p.act _)*_* (k (p.act _))⁻¹; rw [p.act_add]; congr 2; change _= Step.read _ _ (_+0); rw [add_zero]

section
variable (S:StepData c f)
private lemma merit (x y:G.El): G.price (x⁻¹*(y⁻¹)⁻¹)=G.price (x*y⁻¹):=by
 rw [inv_inv,← G.price_inv (x⁻¹*y)]; rw [show (x⁻¹*y)⁻¹=x⁻¹ * (x*y⁻¹)*(x⁻¹)⁻¹ by group]; exact G.price_conj ..
lemma enhanced (W V:spins G c) : trouble S (cane p W) (cane p V)=trouble S W V:=by
 unfold trouble; apply congr_arg
 let e:=Equiv.ofBijective _ ⟨routed p (f:=c), Finite.injective_iff_surjective.mp (routed p)⟩
 refine Fintype.sum_equiv e _ _ ?_
 intro i; simp_rw [swings]; change _= G.price (W (route p _)* (V (route p _))⁻¹)
 unfold swayE; dsimp only; split_ifs <;> first|rfl | (solve|simp only [inv_inv])| exact merit ..
variable (B:S.patch.Branches S.kernel G) (V:spins G c)(hc:Even c.val)
include he B
lemma agreed : ∀ᶠ U:spins G f in 𝓝 1, predictor S (cane p U)=cane p (predictor S U):=by
 have h : Tendsto (orbLift (G:=G) (f:=f)) (𝓝 1) (𝓝 1):=by rw [← Geometry.lift_one (G:=G) (f:=f)]; exact (lift_cont G).tendsto _
 filter_upwards [h.eventually (shared S B (S.withinChoice p 0 (directive S)))] with U hu
 ext1 i; unfold predictor;rw [lifted p U he]
 change _= pull p 0 (orbLift (predictor S U)) i.val; rw [pec S B U he]
 have ht:= S.prediction_channel B p 0 (orbLift U) (directive S); rw [show S.ratio.embed 0 =0 from S.ratio.root.map_zero, hu] at ht; rw [ht]
lemma burn : ∀ᶠ U:spins G f in 𝓝 1, ∀ V:spins G c,bond S (cane p U) (cane p V)=bond S U V:=by
 filter_upwards [agreed p he S B] with U hu V; unfold bond;rw [hu]; exact enhanced ..
lemma turned (H:Flat G f U): ∀ᶠ W:spins G f in 𝓝 U,∀ V:spins G c,bond S (cane p W) (cane p V)=bond S W V:=by
 obtain ⟨k,hk,H⟩:=H
 have hp:Tendsto (goat k) (𝓝 U) (𝓝 1):=by rw [← H]; exact (goat_cont k).tendsto _
 let g:= k ∘ p.act; have hx: compatible g:= compatible_beam p hk
 let v:= k ∘ S.ratio.embed;have hh: compatible v:= by intro i; change k _= _; rw [show S.ratio.embed (-i)=-(S.ratio.embed i) from S.ratio.root.map_neg _]; exact hk _
 have hs:v ∘ p.act=g ∘ S.ratio.embed:=by funext x; exact congr_arg k (Ratio.signed ..)
 filter_upwards [hp.eventually (burn p he S B)] with z hz V
 specialize hz (goat v V);rw [routed_gauges p z k hk, routed_gauges p V v hh,hs] at hz; change bond S (goat g _) (goat (g ∘ S.ratio.embed) _) = _ at hz
 rw [bond_flow S B g hx,bond_flow S B k hk] at hz; exact hz
end
end YM.RegulatorIR.Axial
