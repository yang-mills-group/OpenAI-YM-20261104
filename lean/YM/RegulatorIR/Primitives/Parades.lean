import YM.RegulatorIR.Primitives.Earth
import YM.RegulatorIR.Geometry.Pay
import YM.Lattice.Faces

/-! Root parades for local extensive vertices. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Prim
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Geometry PertExtension Orb Lattice
open scoped Topology ENNReal BigOperators Classical Matrix
variable {U V X Y:Type}{n:Side}

def marching (rips:Motion→Equiv.Perm U)(p:U→V)(b:V→U) (H:∀ d x,p (rips d x)=p x)(h:∀ i,p (b i)=i) (hc:∀ x y,p x=p y→ ∃! d:Motion,rips d x=y): Parade U V:=by
 let R (v: Motion× V):=rips v.1 (b v.2)
 have he v : p (R v)=v.2:=by rw [show R v= rips v.1 (b v.2) from rfl,H,h]
 refine { rips:=rips, bare:=b,rolls:=Equiv.ofBijective R ?_, puts:=fun _=>rfl }
 refine ⟨?_,fun x=>?_⟩
 · rintro ⟨d,i⟩ ⟨e,j⟩ ht; have hr:i=j:=(he (d,i)).symm.trans ((congr_arg p ht).trans (he _))
   subst i; have hy : d=e := (hc (b j) _ (H d _).symm).unique rfl ht.symm; rw [hy]
 obtain ⟨d,h,-⟩:= hc (b (p x)) x (h _); exact ⟨(d,p x),h⟩

def posMarch (H: Even n.val) : Parade (Edge Cover) (OEdge n):= marching (march n) (resolve n) Geometry.position (court_in n) positioned (fun i k h=> motion_eq H i k h)
lemma pos_rips (H : Even n.val) (d i) : (posMarch H).rips d i=court n d i:=rfl
lemma pos_place (H : Even n.val) (i): (posMarch H).bare i=Geometry.position i:= rfl

def unite (A:Parade X Y)(B:Parade U V): Parade (X⊕U) (Y⊕V):= {
 rips:=fun d=>Equiv.sumCongr (A.rips d) (B.rips d)
 bare:=Sum.map A.bare B.bare
 rolls:=(Equiv.prodSumDistrib Motion Y V).trans (Equiv.sumCongr A.rolls B.rolls)
 puts:=by rintro ⟨d,i|i⟩ <;> simp [A.puts,B.puts] }
section Plan
variable {R:Type}[AddCommGroup R][One R]
def ice (p:Face R): Face R:= (-p.1-step p.2.val.1-step p.2.val.2,p.2)
lemma ice_twice (p:Face R) : ice (ice p)=p:=by unfold ice; simp;abel
def plateTrans (r:Four R) (p:Face R): Face R:= (r+p.1,p.2)
lemma iceT (r : Four R)(p:Face R): ice (plateTrans r p)=plateTrans (-r) (ice p):= by unfold plateTrans ice; dsimp only; congr 1;abel
end Plan
lemma plate_ne (H: Even n.val) (p:Face (Per n)): ice p≠p:=by
 rintro he
 let i:=p.2.val.1;let j:=p.2.val.2
 have h:(-p.1-step i-step j : Site n)=p.1:= congr_arg Prod.fst he
 have hs : ((p.1 i):Per n) = -(p.1 i)-1:=by simpa [step_apply,show i≠j from p.2.property.ne] using congr_fun h.symm i
 -- map to ZMod2
 let f:=ZMod.castHom H.two_dvd (Per ((2:ℕ+):Side))
 have hz:= congr_arg f hs
 rw [map_sub,map_neg,map_one] at hz
 let x:= f (p.1 i); change x= -x-1 at hz
 exact (show ∀ x: Per ((2:ℕ+):Side),x≠ -x-1 by decide) x hz

-- face := Torus roof orbits

def ie (x:Face (Per n)):= Classical.choose (p:=fun y=>y=x ∨ y=ice x) (Exists.intro x (Or.inl rfl))
lemma ie_in (x:Face (Per n)): ie x=x ∨ ie x=ice x:=Classical.choose_spec (p:=fun y=>y=x ∨ y=ice x) ⟨x,Or.inl rfl⟩
lemma ie_flip (x:Face (Per n)) : ie (ice x)=ie x:=by unfold ie; congr 1;ext t;rw [ice_twice,or_comm]
lemma ie_open (x:Face (Per n)) : ie (ie x)=ie x:=by rcases ie_in x with h|h <;> simp [h,ie_flip]

abbrev PFace (n:Side):={p: Face (Per n) // ie p=p}
def floorF (n:Side) (p: Face ℤ): Face (Per n):=(wrap n p.1,p.2)
lemma floorI (p:Face ℤ):floorF n (ice p)=ice (floorF n p):=by simp [floorF,ice]
lemma wrap_height (p: Face ℤ)(t:Cover):floorF n (plateTrans (n.val • t) p)= floorF n p:= by refine Prod.ext ?_ rfl; exact congr_arg (Prod.fst : Edge (Site n) → _) (channel_dep n t (p.1, p.2.val.1))
lemma heightE (n:Side) (p v:Face ℤ)(H: floorF n p=floorF n v) :∃! c:Cover,plateTrans (n.val • c) p=v:=by
 obtain ⟨⟨p,b⟩,rfl⟩:= Exists.intro p (rfl : p=p); rcases v with ⟨v,d⟩
 obtain ⟨hx,hv⟩:=Prod.mk.inj H; change b=d at hv; subst d
 obtain ⟨c,h,hc⟩:= channel_eq n (p,b.val.1) (v,b.val.1) (Prod.ext hx rfl);exact ⟨c,Prod.ext (congr_arg (Prod.fst : Edge Cover → _) h.symm) rfl,fun t ht=> hc t (Prod.ext (congr_arg (Prod.fst : Face ℤ → _) ht.symm) rfl)⟩

def placeF (n:Side)(p:Face ℤ):PFace n:=⟨ie (floorF n p), ie_open _⟩
def reachF (p:PFace n): Face ℤ:= (Lattice.lift p.val.1,p.val.2)
lemma floorP (p:PFace n): floorF n (reachF p)=p.val:=by simp [floorF, reachF]
lemma place_reach (p:PFace n): placeF n (reachF p)=p:= Subtype.ext (by change ie (floorF n (reachF p))= _;rw [floorP,p.property])

def windF (n:Side)(d:Motion)(p:Face ℤ): Face ℤ:= match d with
 | across v=> plateTrans (n.val • v) p
 | turn v=> plateTrans (n.val • v) (ice p)
lemma unwindF (n:Side)(d:Motion)(p:Face ℤ): windF n (undo d) (windF n d p)=p:=by
 cases d; simp [undo,windF,plateTrans]; simp [undo,windF,iceT,ice_twice]; unfold plateTrans;simp
def marchF (n:Side)(d:Motion): Equiv.Perm (Face ℤ):= ⟨windF n d,windF n (undo d),unwindF n d,fun p=>by nth_rw 1 [← undo_undo d]; exact unwindF ..⟩
lemma plate_cycle (n:Side)(d: Motion)(x) : placeF n (marchF n d x)=placeF n x:=by apply Subtype.ext; change ie (floorF n (windF n d x))=_;cases d <;> first|(rw [windF, wrap_height, floorI,ie_flip];rfl)|(rw [windF, wrap_height];rfl)
lemma plate_swept (H:Even n.val)(x y:Face ℤ)(h:placeF n x=placeF n y): ∃! d:Motion,marchF n d x=y:=by
 let p:= floorF n x; let q:=floorF n y
 have hv: ie p=ie q :=congr_arg Subtype.val h
 have hx:p=q ∨ ice p=q := by
    rcases ie_in p with h|h <;> rcases ie_in q with h'|h' <;> rw [h,h'] at hv <;> first | exact Or.inl hv| exact Or.inr hv| exact Or.inl ((show Function.Involutive (ice (R:=Per n)) from ice_twice).injective hv)| (exact Or.inr ((congr_arg ice hv).trans (ice_twice _)))
 rcases hx with hq|hq
 · obtain ⟨c,h,hc⟩:= heightE n x y hq; refine ⟨Motion.across c,h,?_⟩; rintro (v|v) hz
   · exact congr_arg Motion.across (hc _ hz)
   have Hq: ice p=p:=(floorI x).symm.trans ((wrap_height (n:=n) (ice x) v).symm.trans ((congr_arg (floorF n) hz).trans hq.symm)); exact (plate_ne H p Hq).elim
 obtain ⟨c,h,hc⟩:= heightE n (ice x) y ((floorI x).trans hq); refine ⟨Motion.turn c,h,?_⟩; rintro (v|v) hz
 · exact (plate_ne H p (hq.trans ((congr_arg (floorF n) hz.symm).trans (wrap_height x v)))).elim
 exact congr_arg Motion.turn (hc _ hz)

def gliders (H:Even n.val): Parade (Face ℤ) (PFace n):= marching (marchF n) (placeF n) reachF (plate_cycle n) place_reach (plate_swept H)
-- torus counting for primitive

def glintEquiv (H:Even n.val): Face (Per n) ≃ PFace n ⊕ PFace n:=by
 refine (Equiv.ofBijective (Sum.elim (Subtype.val : PFace n→Face (Per n)) (ice ∘ Subtype.val)) ?_).symm
 refine ⟨?_,?_⟩
 · have ht (p v:PFace n) : p.val≠ ice v.val:= by intro h; have hh:=p.property; rw [h,ie_flip,v.property] at hh; exact plate_ne H _ hh.symm
   rintro (i|i) (j|j) hx <;> first|exact congr_arg Sum.inl (Subtype.ext (show i.val=j.val from hx))|exact congr_arg Sum.inr (Subtype.ext ((show Function.Involutive (ice (R:=Per n)) from ice_twice).injective hx))|exact (ht i j hx).elim|exact (ht j i hx.symm).elim
 intro p; let v:PFace n:=⟨ie p,ie_open _⟩;rcases ie_in p with h|h
 · exact ⟨.inl v,h⟩
 exact ⟨.inr v,(congr_arg ice h).trans (ice_twice _)⟩
lemma plate_both (H:Even n.val) (f:Face (Per n)→ℝ)(h:∀ i,f (ice i)=f i): (∑ i,f i)=2*∑ i:PFace n,f i.val:=by
 rw [← (glintEquiv H).symm.sum_comp, Fintype.sum_sum_type];change (∑ i:PFace n,f i.val)+(∑ i:PFace n,f (ice i.val))=_;simp_rw [h]; rw [two_mul]
end YM.RegulatorIR.Prim
