import YM.MS.Theater.HoloK

set_option autoImplicit false
noncomputable section
namespace YM.MS.Theater
open Set Function Filter Finset Metric MeasureTheory Real Maxwell Labels
open Analysis Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Woven Color
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {G:Gauge} {h n r:ℕ} {u x v:ℤ} {p:Pol G} {F H:Law G} {f:Local.BV.Grade G}
lemma paidConj (n:ℕ): star ( hitϑ n * ((-1:ℂ)^n) )=hitϑ n:= by unfold hitϑ; rw [← mul_pow,star_pow]; simp
lemma overθ (x:Witness G h)(hp:∀ i,star (x i)=x i): over ( RowLeg G h x )= RowLeg G h x:= by
    funext i; rcases i with ⟨⟨⟨_|i,_|_⟩,t⟩,p⟩ <;> first| exact (star_zero ℂ) | skip
    have he : speak (h+1) i (-p) ( cl G t )=(-1:ℝ)^(h+1) • speak ( h+1 ) i p ( cl G t ):= Eq.trans ( congr_arg (fun v:FourP=> speak ( h+1 ) i v ( cl G t )) ( neg_one_smul ℝ p ).symm ) ( plane_x ( a:=(-1:ℝ) ) i p _ )
    let L:= yard G h; let V:=speak (h+1) i p (cl G t); change star ( hitϑ ( h+1 ) * x ( L ( speak (h+1) i (-p) ( cl G t ) )) )=_; rw [ he,map_smul,map_smul, Complex.real_smul ]; push_cast; rw [ ← mul_assoc,star_mul',hp,paidConj ]; rfl
lemma conjugated (P:Pol G): orbit G (conjPol P)= overC (orbit G P):= by
    unfold conjPol; induction P using MvPolynomial.induction_on with
    | C x=> rw [ MvPolynomial.map_C,cus,cus ]; ext l; rcases l with _|⟨x,l⟩; rfl; change _= star (coin _ (_::_)); exact Eq.symm (star_zero _)
    | mul_X P i ih=> rw [_root_.map_mul,MvPolynomial.map_X,bags,bags,cusp,ih, Lifting.over_p, Lifting.overM, ( overθ ( pick i ) ( fun x=>by simp [pick] ))] -- lamp
    | add P Q ih hv=> rw [map_add,map_add,map_add,map_add,ih,hv]
lemma coloredP (hp:At p (h,r)): (∀ u:G.El, repeatC u (orbit G p)=orbit G p) ↔ p∈ Labels.invariantSpace G:= by
   constructor; · intro h A u; have hz : changed (fun _=>Labels.Taylor.paint u ) p=p:= opaqueL ( still (fun _=>Labels.Taylor.paint u) hp ) hp ( Eq.trans (labelU u p).symm (h u)); exact Eq.trans ( eval_changed (fun _=>Labels.Taylor.paint u) A p ).symm ( congr_arg _ hz ) -- `read` orientation
   intro h u; rw [labelU]; congr 1; apply Labels.eval_ext; intro A; rw [eval_changed]; exact h A u
lemma bar_still (hp:At p (h,r)): At (Labels.conjPol p) (h,r):= by
    apply MvPolynomial.IsWeightedHomogeneous.induction_on (motive:=fun (p:Pol G) _=> At ( Labels.conjPol p ) (h,r)) _ _ _ ( (nodeId _ _).mp hp ); · unfold Labels.conjPol; rw [map_zero]; exact zero_mem _
    · intro f t h1 h2 h f'; unfold Labels.conjPol; rw [map_add]; exact add_mem h f'
    intro d s ht; rw [ Labels.conjPol,MvPolynomial.map_monomial ]; exact MvPolynomial.isWeightedHomogeneous_monomial _ _ _ ht
lemma scalePaid (hp:At p (h,r)): Bright (orbit G p) ↔ (p∈Labels.invariantSpace G ∧ Labels.conjPol p=p):= by
    refine ⟨?_,?_⟩; · intro h; exact ⟨( coloredP hp ).mp h.color, opaqueL ( bar_still hp ) hp (by rw [conjugated,h.shadow]) ⟩
    rintro ⟨h,h'⟩; exact ⟨ (setting_K hp).2,( coloredP hp ).mpr h,by rw [← conjugated,h'] ⟩
open Physical
lemma rebate (hp: F∈Allowed G u n)(h:F∈ PastSym G u n): F∈ Null G u n:= by
   obtain ⟨f,⟨hh,hS⟩,rfl⟩:= h; have hv := Color.hue ( F:=f ) hS; let U:= Color.pale (Color.mean f ); have he := hp.2; -- hp.2 maybe invalid
   have hf : Bright ( natQ f ):= hp.2; refine ⟨ hp,U, (?_:U∈ Lease G (u-1) n (-1)),?_⟩
   · have he: f∈Bed G ((u-1)-(-1)) (-1) n:= by rw [show u-1-(-1)=u from (by omega)]; exact hh
     exact ( byGuide _ ).mpr ⟨ smul_mem _ _ ( add_mem ( convert_sig he ) ( staid ( convert_sig he )) ), hv ⟩
   change natQ U=natQ f; unfold U; rw [ pale_Q, show natQ ( Color.mean f )= _ from Eq.symm ( Color.mean_charge id ), Color.mean_identity hf.color, pale_identity hf.shadow ]
lemma Governed (hP: At p (h,r)): ( orbit G p∈ Allowed G h r ) ↔ ( p∈ Labels.invariantSpace G ∧ Labels.conjPol p=p):= by rw [ ← scalePaid hP ]; exact ⟨ fun h=> ( byGuide _ ).mp h|>.2, fun h=> (byGuide _).mpr ⟨ ( setting_K hP ).1,h⟩ ⟩
lemma certN (hp:At p (h,r))(hv:orbit G p∈ Allowed G h r): orbit G p∈ Null G h r ↔ Maxwell.reduceEq p=0:= by
   refine ⟨?_,fun H=> rebate hv ((onward hp).mpr H) ⟩; rintro ⟨_, F,H,hf⟩; rw [← onward hp]; have hm : Bed G (( ( h:ℤ )-1)-(-1)) (-1) r= Bed G h (-1) r:= by rw [show ( ( h:ℤ )-1-(-1))=h from (by omega)] -- wrong underscore elaboration
   obtain ⟨he,hc⟩:= ( byGuide _ ).mp H; rw [ hm ] at he; exact ⟨ _,⟨ he,hc.weight ⟩,hf⟩
end YM.MS.Theater
