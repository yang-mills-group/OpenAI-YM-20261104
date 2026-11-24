import YM.RegulatorIR.Address.Count
import YM.RegulatorIR.Budget.Covariance
import YM.PertExtension.OrbTree

/-!
Canonical orbit and chamber. One scalar/color coordinate per independent
quotient link. m x eq signed. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Geometry
open Finset Function Lattice PertExtension Orb Gauge Budget Tuple Budget.Tuple Budget.Packet Motion Spatial
open scoped ENNReal NNReal BigOperators Classical Topology
variable {n: Side}

def reco (x:Edge Cover) : Edge Cover:= (-x.1-step x.2,x.2)
def around (n:Side) (x:Edge Cover): Edge (Site n):=(wrap n x.1,x.2)
@[simp] lemma reco_twice (x:Edge Cover): reco (reco x)=x:=by unfold reco; simp
lemma reco_edge (x:Edge Cover): around n (reco x)= reflect (around n x):=by unfold around reco reflect;simp

-- displacement by Cover

def dis (v:Cover)(x: Edge Cover): Edge Cover:=(v+x.1,x.2)
lemma dis_reco (v:Cover)(x:Edge Cover): reco (dis v x) = dis (-v) (reco x):=by unfold reco dis; simp only [neg_add]; congr 1;abel
def glint (l:ℝ)(b:Axis):Room:= (1/2:ℝ) • slide l (step b)
def seat (l:ℝ)(x:Edge Cover): Room:= slide l x.1 + glint l x.2
lemma dis_seat (l:ℝ)(v:Cover)(x:Edge Cover): seat l (dis v x)=slide l v+seat l x:=by simp [dis,seat,add_assoc]
lemma seat_reco (l:ℝ)(x:Edge Cover): seat l (reco x)=-seat l x:=by unfold seat glint reco; simp only [map_sub,map_neg]; module
lemma turns_site (l:ℝ) (v:Cover): slide l (n.val • v) = slide (l*n.val) v:=by ext a; simp; ring
lemma channel_dep (n:Side)(v:Cover)(e:Edge Cover): around n (dis (n.val • v) e)=around n e:=by
 have h : wrap n (n.val • v)=0:=by rw [map_nsmul]; funext i; change (n.val • (wrap n v) i)=0; rw [nsmul_eq_mul];simp [Per]
 unfold around dis;rw [map_add,h, zero_add]
lemma channel_eq (n:Side) (x y:Edge Cover)(he:around n x=around n y): ∃! v:Cover, y=dis (n.val • v) x:=by
 obtain ⟨h,h'⟩:=Prod.mk.inj he; change wrap n x.1=wrap n y.1 at h
 choose v hv using fun i:Axis=> (show (n.val:ℤ) ∣ y.1 i-x.1 i from (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp (congr_fun h i))
 have hp:y=dis (n.val • v) x:= by
   refine Prod.ext ?_ (show y.2=(dis (n.val • v) x).2 from h'.symm); funext i;change y.1 i=n.val • v i+ x.1 i; rw [nsmul_eq_mul]; linarith [hv i]
 refine ⟨v,hp,fun q hq=>?_⟩
 have H: q=v:=by
    have hx:n.val • q=n.val • v:=add_right_cancel (congr_arg Prod.fst (hq.symm.trans hp))
    exact smul_right_injective Cover (by exact_mod_cast n.property.ne') hx
 exact H

-- inversion ambiguity 

def resolve (n:Side)(x:Edge Cover): OEdge n:=index (around n x)
def position {n:Side}(x:OEdge n) : Edge Cover:= (Lattice.lift x.val.1,x.val.2)
lemma position_edge {n:Side} (x: OEdge n): around n (position x)=x.val:=by unfold around position; simp
lemma positioned {n:Side}(x:OEdge n): resolve n (position x)=x:=by rw [resolve,position_edge]; exact Subtype.ext x.property
lemma tandem (n:Side)(x y:Edge Cover): resolve n x=resolve n y ↔ around n x=around n y ∨ around n x=reflect (around n y) :=by
 change index _=index _ ↔ _; constructor
 · intro he
   let p:= around n x; let q:=around n y; have h:eR p=eR q:= congr_arg Subtype.val he
   change p=q∨p=reflect q
   rcases eR_spec p with hp|hp <;> rcases eR_spec q with hq|hq <;> rw [hp,hq] at h
   · exact Or.inl h
   · exact Or.inr h
   · exact Or.inr (by nth_rw 1 [← reflect_reflect p];rw [h])
   exact Or.inl (by nth_rw 1 [← reflect_reflect p];rw [h, reflect_reflect])
 rintro (h|h)
 · rw [h]
 rw [h]; exact Subtype.ext (eR_reflect _)

def shade (n:Side)(x:Edge Cover):ℝ:= if eR (around n x)=around n x then 1 else -1
lemma dawning (x:OEdge n):shade n (position x)=1:=by unfold shade;exact if_pos (by rw [position_edge,x.property])
lemma shade_reco (x:Edge Cover)(he:Even n.val): shade n (reco x)= -shade n x:=by
 unfold shade; rw [reco_edge,eR_reflect]; rcases eR_spec (around n x) with h|h <;> rw [h]
 · simp [no_fixed_edge he (around n x) |>.symm]
 simp [no_fixed_edge he]

def court (n:Side) (d: Motion) (x:Edge Cover): Edge Cover:= match d with
 | Motion.across v=>dis (n.val • v) x
 | Motion.turn v=>dis (n.val • v) (reco x)
lemma court_in (n:Side)(d:Motion)(x:Edge Cover): resolve n (court n d x)= resolve n x:=by
 cases d
 · rw [court, resolve,channel_dep]; rfl
 rw [court]; apply (tandem ..).mpr; exact Or.inr ((channel_dep ..).trans (reco_edge ..))
lemma court_inv (n:Side)(d : Motion)(x:Edge Cover): court n (undo d) (court n d x)=x:= by
 cases d with
 | across v=>simp [court,undo,dis]
 | turn v=>rw [court,undo,court, dis_reco, reco_twice]; simp [dis]
def march (n:Side)(d:Motion): Equiv.Perm (Edge Cover):= ⟨court n d,court n (undo d),court_inv n d,fun x=>by nth_rw 1 [← undo_undo d]; exact court_inv ..⟩
lemma shift_out (l:ℝ)(d:Motion)(e:Edge Cover):seat l (court n d e)=Motion.loc (l*n.val) d (seat l e):=by cases d <;> simp only [court, dis_seat,turns_site,seat_reco,Motion.loc]
lemma shade_court (H:Even n.val)(d:Motion)(e:Edge Cover):shade n (court n d e)=Motion.sign d*shade n e:=by
 cases d
 · simp only [court,shade,sign,channel_dep, one_mul]
 next i=>
    rw [court,shade,channel_dep]; change shade n (reco e)=_
    rw [shade_reco e H]; simp [Motion.sign]
lemma motion_eq (H:Even n.val) (x y:Edge Cover)(he:resolve n x=resolve n y): ∃! d:Motion, court n d x=y:=by
 let p:= around n x; let q:= around n y
 rcases (tandem ..).mp he with hx|hx
 · obtain ⟨v,hv,Hv⟩:=channel_eq n x y hx; refine ⟨across v,hv.symm,?_⟩
   rintro (w|w) hw
   · exact congr_arg Motion.across (Hv w hw.symm)
   have hh : p=reflect p:= hx.trans ((congr_arg (around n) hw.symm).trans ((channel_dep n w _).trans (reco_edge x)))
   exact (no_fixed_edge H p hh.symm).elim
 have hx' : around n (reco x)=around n y:=by rw [reco_edge,hx, reflect_reflect]
 obtain ⟨v,hv,Hv⟩:=channel_eq n (reco x) y hx'; refine ⟨turn v,hv.symm,?_⟩; rintro (w|w) hw
 · have hh:p=q:= (channel_dep n w x).symm.trans (congr_arg (around n) hw)
   exact (no_fixed_edge H q (hx.symm.trans hh)).elim
 exact congr_arg Motion.turn (Hv w hw.symm)

-- attach color dimensions
abbrev Long (X:Type):= Edge Cover × X
abbrev Hatch (n:Side)(X:Type):= OEdge n × X

def Cart (l P:ℝ)(X:Type)(H:Even n.val)(h:l*n.val=P): Deck P (Long X) (Hatch n X) where
 pos x:= seat l x.1
 orbit x:= (resolve n x.1,x.2)
 place z:= (position z.1,z.2)
 placed x:=Prod.ext (positioned x.1) rfl
 wind d:= Equiv.prodCongr (march n d) (Equiv.refl X)
 neutral x:=by rcases x with ⟨a,b⟩; simp [march,court,dis]
 reversed d:=by ext1 x; change (court n _ x.1,x.2)=(court n _ x.1,x.2); rfl
 projected d x:= Prod.ext (court_in n d x.1) rfl
 displaced d x:= h ▸ shift_out l d x.1
 edges x y he:=by obtain ⟨hh,h'⟩:= Prod.mk.inj he; obtain ⟨d,hg,hd⟩:= motion_eq H x.1 y.1 hh; exact ⟨d,Prod.ext hg h', fun g hv=> hd g (congr_arg Prod.fst hv)⟩
 orient x:= shade n x.1
 north x:= dawning x.1
 retreat d x:= shade_court H d x.1
end YM.RegulatorIR.Geometry
