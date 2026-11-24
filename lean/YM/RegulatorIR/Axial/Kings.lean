import YM.RegulatorIR.Axial.Slots

/-!
# Constant adjoint lift, Signed-axis orbit lift for W1 on cover
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Axial
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight PowerSeries Gain Prim Motion Budget.Packet Budget.Deck Finset
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries
variable {f:Side}{G:Gauge}
section Route
variable (p:Signed) (A:BEdge G)
def beatT (p:Signed)(x:Horizon G f)(i:OEdge f): G.Color:=if blink p i.val then -fire x (sent p i.val) else fire x (sent p i.val)
def beast (p:Signed)(A:BEdge G)(e:Edge Cover): G.Color:=if p.flip e.2 then -A (rotateE p e) else A (rotateE p e)
lemma beat_flipped (x: Horizon G f) : climb x=fun u=>G.lieExp (x u):=rfl
lemma liftExp (x:Horizon G f)(i:Edge (Site f)) : orbLift (climb x) i=G.lieExp (fire x i):=by unfold orbLift fire liftLinks;split; rfl;rw [Work.F03.exp_neg_color];rfl
lemma beat_rose (x:Horizon G f)(t:ℝ) : climb (t • beatT p x)= cane p (climb (t • x)) :=by
 ext1 i; rw [cane,look]; simp_rw [liftExp]; change G.lieExp (t • beatT p x i)= _; rw [beatT];let q:=sent p i.val; have h:fire (t • x) q=t • fire x q:=by unfold fire;split <;> first| (rw [smul_neg]; rfl)|rfl
 split <;> rw [show fire (t • x) (sent p i.val)=_ from h]; rw [smul_neg]; exact Work.F03.exp_neg_color ..
lemma beat_half (x:Horizon G f) (H:Even f.val) (i:Edge (Site f)): fire (beatT p x) i= if blink p i then -fire x (sent p i) else fire x (sent p i):=by
 rcases eR_spec i with h|h
 · have he : i=(index i).val:=h.symm; nth_rw 1 [he];rw [fire_at,beatT,← he] -- h rew? check
 have hx : (index i).val=reflect i:=h
 have ht:= fire_at (beatT p x) (index i)
 rw [show beatT p x (index i) = ( if blink p (index i).val then -fire x (sent p (index i).val) else fire x (sent p (index i).val)) from rfl,hx,fire_swaps _ H, show blink p (reflect i)=blink p i from rfl,sent_there,fire_swaps _ H _] at ht -- unfolds issue
 rw [← neg_inj,ht];split <;> simp

variable (S:Finset (Edge Cover))(h:4 ≤ f.val)(hp:Even f.val)(hA:Function.support A⊆(↑S:Set _))
def flaming (z:Side): Horizon G (rep f z):= beatT p⁻¹ (track z h A)
lemma sent_inverse (i:Edge (Site f)): sent p⁻¹ (sent p i)=i:=by
 let v:=Geometry.position (index i)
 obtain ⟨x,rfl⟩:∃ x:Edge Cover,around _ x=i:=⟨(Lattice.lift i.1,i.2),Prod.ext (wrap_lift _) rfl⟩
 rw [← brought,← brought,reverted]
include hp
lemma track_beast (z:Side)(v:Edge Cover)(he:inside z v.1): fire (flaming p A h z) (secure p f z (rotateE p v)) = beast p⁻¹ A (rotateE p v):=by
 let u:=rotateE p v
 unfold flaming; rw [beat_half p⁻¹ _ (hp.mul_left _), show secure _ _ _ _= around _ (shifting p f z u) from rfl,step_cover, show around _ (shifting p f z u)=sent p (around _ (deep f z v)) from secured ..,sent_inverse, track_link z h A v he]; unfold beast;rw [reverted];rfl
omit hp
include hA
lemma track_rose (z:Side)(u:OEdge (rep f z))(ht: flaming p A h z u≠0): ∃ i∈ S.image (rotateE p),sig p f z i=u:=by
 have he: track z h A (route p⁻¹ u)≠0:= by
   intro hg; apply ht; unfold flaming beatT; have hx: fire (track z h A) (sent p⁻¹ u.val)=0:=by
       unfold fire; split
       · exact hg
       rw [show track z h A (index (sent p⁻¹ u.val))=0 from hg,neg_zero]
   rw [hx]; simp
 obtain ⟨i,hi,hh⟩:= track_here A h S hA z (route p⁻¹ u) he; rw [sig,step_one] at hh -- hh points raw index
 let y:= sig p f z (rotateE p i)
 have hp:∀ u:OEdge (rep f z),route p⁻¹ (route p u)=u:=by
    intro u; unfold route;let t:=sent p u.val
    rcases eR_spec t with ht|ht
    · change index (sent p⁻¹ (eR t))= _;rw [ht,show sent p⁻¹ t=u.val from sent_inverse ..]; exact Subtype.ext u.property
    change index (sent p⁻¹ (eR t))=_; rw [ht, sent_there,show sent p⁻¹ t=u.val from sent_inverse ..]; exact Subtype.ext ((eR_reflect ..).trans u.property)
 have hz:= line_route p f z i; refine ⟨rotateE p i, mem_image_of_mem _ hi,(routed p⁻¹) ?_⟩; rw [←hz,hp,hh]

include hp

def bookT : Brief p f (fun z _=>flaming p A h z) (vow (fun _=> hue (beast p⁻¹ A))):=by
 let P:= S.image (rotateE p); refine { stampK:=P,suited:=?_,sky:=Eventually.of_forall fun _=> contDiffAt_const,endQ:=Eventually.of_forall (fun z=> receipt (p:=p) (X:=fun z _=>flaming p A h z) P z (fun _=>track_rose p A S h hA z)),pays:=?_ }
 · intro x hx; have he: x.1∈ P:=by
       let q:= rotateE p⁻¹ x.1
       have hh : A q ≠0:=by
          intro h; apply hx; change tale (fun _=> beast p⁻¹ A _ _)= _; have hp : beast p⁻¹ A x.1=0:=by unfold beast;rw [show A (rotateE p⁻¹ x.1)=0 from h];simp
          simp [hp,tale_const]
       exact mem_image.mpr ⟨q,hA hh, (revol p).apply_symm_apply _⟩
   exact ⟨(⟨x.1,he⟩,x.2),rfl⟩
 refine eventually_all.mpr fun x=>?_
 let b:=x.1.val
 obtain ⟨v,hv,he⟩:= mem_image.mp (show b∈ P from x.1.property);filter_upwards [included v.1] with z hz
 change tale (fun _=> fire (flaming p A h z) (secure p f z b) x.2)= tale (fun _=> beast p⁻¹ A b x.2)
 simp_rw [←he,track_beast p A h hp z v hz]
end Route
section Royal
variable (A:BEdge G)(u:G.El)

def sbadge (A:Horizon G f): Horizon G f:= fun i=> G.adjoint u (A i)
def vbadge (A:BEdge G): BEdge G:= fun i=> G.adjoint u (A i)
lemma shinesB (v:G.Color): G.lieExp (G.adjoint u v)= u*G.lieExp v*u⁻¹:=by apply G.mat_injective;simp_rw [Gauge.mat_mul,mat_lieExp, Gauge.mat_adjoint,Gauge.exp_conjugate, Gauge.mat_inv];rfl
lemma sentB (p:Horizon G f)(t:ℝ) : climb (t • sbadge u p)= goat (fun _=>u) (climb (t • p)):=by
 ext1 i; rw [goat_at]; change G.lieExp (t • G.adjoint u (p i))= u*_ * u⁻¹; rw [← map_smul]; exact shinesB u _
lemma fireBorn (p:Horizon G f)(i:Edge (Site f)): fire (sbadge u p) i=G.adjoint u (fire p i):=by unfold fire; split; rfl; rw [map_neg];rfl
variable (S:Finset (Edge Cover))(h:4 ≤ f.val)(hA:Function.support A⊆(↑S:Set _))
include hA
lemma sizesA : Function.support (vbadge u A)⊆ ↑S:=fun x hx=>hA (a:=x) (fun h=> hx (by unfold vbadge;rw [h,map_zero]))
def bookA : Brief 1 f (fun z _=> sbadge u (track z h A)) (vow (fun _=>hue (vbadge u A))):=by
 refine { stampK:= S,suited := (scriptT (vbadge u A) h S (sizesA A u S hA)).suited, sky:=Eventually.of_forall fun _=>contDiffAt_const,endQ := ?_, pays:=?_ }
 · exact Eventually.of_forall fun z=> receipt (p:=1) (X:=fun z _=>sbadge u (track z h A)) S z (fun t i hx=> track_here A h S hA z i (fun h'=>hx (by unfold sbadge; rw [h',map_zero])))
 refine eventually_all.mpr fun i=>?_
 let j:= wire S i; filter_upwards [included j.1.1] with z hz
 change tale (fun t=> fire (sbadge u _) (secure _ _ _ j.1) _)= _;simp_rw [fireBorn, step_one, track_link z h A _ hz];rfl
end Royal
end YM.RegulatorIR.Axial
