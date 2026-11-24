import YM.RegulatorIR.Tape.Hound

/-!
# Repeat auxiliaries for Ward verification
Canonical axis-order forest coherent across repeating the entire period. Carries
quadratic obligations on any such repeat. Not uniform conclusions, not yet
about varying trajectories. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Halo
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim Finset PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step
open scoped Topology ENNReal BigOperators Classical PowerSeries ContDiff
variable {G:Gauge}{f c n m:Side}

def castSite (m n:Side) : Site (m*n) →+ Site n where
 toFun x i:=ZMod.castHom (show n.val∣(m*n).val from dvd_mul_left ..) (Per n) (x i)
 map_zero':=by ext1 i; exact RingHom.map_zero _
 map_add' x y:=by ext1 i; exact RingHom.map_add ..

def castEdge (m n: Side) (e:Edge (Site (m*n))): Edge (Site n):= (castSite m n e.1,e.2)
lemma falls (x:Cover): castSite m n (wrap (m*n) x)=wrap n x := by ext1 i; exact map_intCast (ZMod.castHom (show n.val∣(m*n).val from dvd_mul_left ..) (Per n)) (x i)
lemma fallen (x:Edge Cover): castEdge m n (around _ x)= around n x:=Prod.ext (falls _) rfl
lemma val_step (n m:Side)(i:Axis): castSite m n (Lattice.step i)=Lattice.step i:=by rw [← wrap_step (m*n),falls,wrap_step]
lemma reflectsE (u:Edge (Site (m*n))): castEdge m n (reflect u)= reflect (castEdge m n u):=by simp [reflect,castEdge,map_sub,val_step]

section Step
variable (m:Side)(S:StepData c f)

def climbS (S:StepData c f) (m:Side): StepData (m*c) (m*f):= { patch:=S.patch,kernel:=S.kernel, sizes:=by rw [show (m*f).val=m.val*f.val from rfl,S.sizes,← mul_assoc]; rfl }
def bios (S:StepData c f) :Tree.Forest S.ratio:= Bark.proper S.ratio S.patch.odd_side
lemma filial (x:Site (m*f)): slot (climbS S m).ratio x=slot S.ratio (castSite m f x):=by
 have he: (climbS S m).ratio.count=S.ratio.count:=rfl
 obtain ⟨y,HY⟩:∃ y,wrap (m*f) y=x:= ⟨_, wrap_lift x⟩; rw [← HY,falls]; unfold slot; rw [Ratio.residue_wrap,Ratio.residue_wrap];rfl
lemma leaf_in (x:Site (m*f)): leaf (climbS S m).ratio x↔ leaf S.ratio (castSite m f x):=by
 unfold leaf; simp only [ne_eq,Ratio.root_id]; obtain ⟨y,HY⟩:∃ y,wrap _ y=x:= ⟨_,wrap_lift x⟩;rw [← HY,falls, Ratio.residue_wrap, Ratio.residue_wrap];rfl
lemma moves (x:Site (m*f)): (bios (climbS S m)).up x=(bios S).up (castSite m f x):= by
 let Q:=(climbS S m).ratio
 change (if h:leaf Q x then toward Q x h else _) = _
 unfold bios Bark.proper
 dsimp only;split
 next h=>
   let hx:= (leaf_in m S x).mp h; rw [dif_pos hx];
   have he: slim Q x h=slim S.ratio (castSite m f x) hx:=by unfold slim; congr 1; simp only [active,Q,filial]
   simp only [toward,he];rw [show slot Q x=_ from filial m S x]
 next h=> rw [dif_neg (show ¬leaf _ (castSite m f x) from mt (leaf_in m S x).mpr h)]
lemma trunk_iff (u:Edge (Site (m*f))): u∈ (bios (climbS S m)).trunks ↔ castEdge m f u∈ (bios S).trunks:=by
 let c':= castSite m f
 let A:=bios S; let B:=bios (climbS S m)
 have hv (x:Site (m*f)) (i:Lattice.Step) : castEdge m f (i.used x)=i.used (c' x):= by unfold castEdge Lattice.Step.used;split_ifs <;> first|rfl | (simp only [map_sub,val_step];rfl)
 rw [B.trunk_mem_iff,A.trunk_mem_iff]; constructor
 · rintro ⟨x,hx,rfl⟩; exact ⟨c' x,(leaf_in m S x).mp hx,by rw [show B.up x=A.up (c' x) from moves m S x,hv]⟩
 rcases u with ⟨x,u⟩; rintro ⟨y,hy,hh⟩; generalize hx:A.up y=d at hh; rcases d with ⟨i,b|b⟩
 · obtain ⟨rfl,rfl⟩:= (show y=c' x ∧ i=u from Prod.mk.inj hh); -- substitutes?
   exact ⟨x,(leaf_in m S x).mpr hy,(by rw [show B.up x=A.up (c' x) from moves ..,hx]; rfl)⟩
 obtain ⟨hg,rfl⟩:= (show y - step i=c' x ∧ i=u from Prod.mk.inj hh)
 let w:= x+step i; have hw:c' w=y:=by unfold w c'; rw [map_add, val_step,← show y-step i= _ from hg,sub_add_cancel]
 refine ⟨w,(leaf_in m S w).mpr (hw ▸ hy),?_⟩
 rw [show B.up w=A.up (c' w) from moves ..,hw,hx]; change (w-step i,i)=(x,i); unfold w;simp

variable {G:Gauge}
lemma shift_at (x): branch (bios (climbS S m)) (resolve _ x)=branch (bios S) (resolve _ x):=by
 apply propext
 unfold resolve;rw [bone (F:=bios (climbS S m)) (Field.Square.proper ..),bone (F:=bios S) (Field.Square.proper ..),trunk_iff,fallen]
lemma axi (L:Scale): prism (G:=G) (climbS S m) (bios (climbS S m)) L=prism S (bios S) L:=by
 ext1 x; cases x
 next x=>ext1 t; ext1 v; change carnal _ _ x t v=carnal _ _ x t v; simp_rw [carnal,shift_at]
 rfl
lemma needles : fringe (X:=G.ColorIndex) (climbS S m)=fringe S:= rfl -- G not type
end Step

variable (m n:Side)
def filling (m:Side): Motion→Motion
 | .turn v=>.turn (m.val • v)
 | .across v=>.across (m.val • v)
lemma filling_v (x:Edge Cover)(d:Motion) : court n (filling m d) x=court (m*n) d x:=by cases d <;> rw [filling,court,court,smul_smul,Nat.mul_comm] <;> rfl
lemma sign_fill (d:Motion): Motion.sign (filling m d)=Motion.sign d:=by cases d <;> rfl

section Pride
variable (S:StepData c f)(A B C D:ℝ) -- simplify
lemma arrange {P P' R l:ℝ}(hf:Even f.val)(hc:Even c.val)(he:Even (m*f).val)(hh:Even (m*c).val)(HL:l*f.val=P)(HR:R*c.val=P)(H:l*(m*f).val=P')(hp:R*(m*c).val=P')
 {K N:Layer (Foot G) (Foot G)}{K' D:Layer (Foot G) (Foot G)}
 (HV:Bedload (Carto G l P hf HL) (Carto G R P hc HR) S.kernel.penalty (awake S (bios S)) K K' (finer (fringe S)) D N):Bedload (Carto G l P' he H) (Carto G R P' hh hp) (climbS S m).kernel.penalty (awake (climbS S m) (bios (climbS S m))) K K' (finer (fringe (climbS S m))) D N := by
 let A:=Carto G l P hf HL;let B:=Carto G R P hc HR; let C:=Carto G l P' he H;let F:=Carto G R P' hh hp; let p:= awake (G:=G) S (bios S); let u:=climbS S m;let w:= awake u (bios u) (G:=G)
 have hg (x: Foot G): w (C.orbit x)=p (A.orbit x):= congr_arg Not (shift_at m S x.1)
 have Hl (d:Motion) (x:Foot G): C.wind d x=A.wind (filling m d) x:= Prod.ext (filling_v ..).symm rfl
 have Hr (d:Motion) (x:Foot G): F.wind d x=B.wind (filling m d) x:= Prod.ext (filling_v ..).symm rfl
 have ht:= HV.sym
 have hs:w ∘ C.orbit=p∘A.orbit:=funext hg
 have hb:finer (fringe S)=finer (fringe u (X:=G.ColorIndex)):=rfl
 refine { rows:=HV.rows,sym:= ⟨?_,?_,?_,?_⟩, symmetric:=HV.symmetric, mean:=?_, inverse:=?_, sheet:=?_, feather:=?_, energy:=HV.energy }
 · intro d x y; rw [show _=_ from Hl d x,show _=_ from Hl d y]; exact ht.1 ..
 · intro d x y; rw [show _=_ from Hr d x,show _=_ from Hl d y]; exact ht.2.1 ..
 · intro d x y; rw [show _=_ from Hl d x,show _=_ from Hr d y]; exact ht.2.2.1 ..
 · intro d x y; rw [show _=_ from Hl d x,show _=_ from Hl d y]; exact ht.2.2.2 ..
 · intro x y; change ¬w (C.orbit x)→_; rw [hg]; exact HV.mean x y
 · intro x y; change ¬w (C.orbit x)→ _; rw [hg];exact HV.inverse x y
 · rw [show awake (climbS S m) _∘ (Carto G l P' he H).orbit=_ from hs];exact HV.sheet
 rw [show awake (climbS S m) _∘ (Carto G l P' he H).orbit= _ from hs];exact HV.feather
end Pride
end YM.RegulatorIR.Halo
