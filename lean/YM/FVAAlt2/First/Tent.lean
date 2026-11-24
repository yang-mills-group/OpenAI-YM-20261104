import YM.SchemeConversionRG11.Coupling.Meter
import YM.FVAAlt2.First.Leads
/-! Full correspondence of (finite horizon) tangent Lie actions on real frames.
 After proving position-normalized leading arrays and through1 postures, this controls Peal exactly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.First.Tent
open Function Set Filter Finset Topology Lattice
open Precision Extra.FD Maxwell Labels Extraction
open FormalOPE FormalOPE.RG10.Gazebo FormalOPE.RG10.Position
open Pert Pert.Position
open PertExtension PertExtension.LatticePT PertExtension.Position PertExtension.Physical
open Home
open scoped BigOperators Classical Topology
variable {G:Gauge}{F:Frames G}{d k:ℕ}
local notation "J"=> RG10.Position.Deck F d
local notation "K"=> deck F d
local notation "E"=> Pert.Position.E F d
variable (b:tents F d)
private def hop (A:FrameAt J ℝ) : Module.End ℂ (E):= Physical.operator (L:=Maxwell.standard F) K A
lemma op_at(A:FrameAt J ℝ)(i:J): hop A (K i)=∑ j:J,(A i j:ℂ) • K j:= Physical.operator_basis (L:=Maxwell.standard F) K A i
lemma buf_at (i:J): (RG10.Gazebo.buf b).val (deck F d i)=∑ j:J,b.val i j • K j:= by
 change hop b.val _= _; rw [ op_at ]; simp
variable (w:Pert.Position.Buffer F d)
def cmS := cmotor F w- LinearMap.id
lemma cmS_at (x:E): cmS w x=w.val x:= by
 change x+w.val x-x=w.val x; abel
def ticket (i j:J):ℝ:= ((K).repr (w.val (K i)) j).re
lemma ticket_r(i j:J) : (↑(ticket w i j):ℂ)= (K).repr (w.val (K i)) j:= Home.clBasis _ ((freeTable F).conj (table_spin F) d) ( RG10.Position.deck_real F d ) (by rw [ w.property.2.2.1, RG10.Position.deck_real F d i ]) _
lemma ticket_h(i:J): ∑ j:J,(ticket w i j:ℂ) • K j=w.val (K i):= by simp_rw [ticket_r]; exact (K).sum_repr _
lemma tic_oper : hop (ticket w)=cmS w:= by apply (deck F d).ext; intro i; rw [ op_at,cmS_at ]; exact ticket_h w i
lemma tic_lower (i j:J)(he: RG10.Position.Deck.price F d i< RG10.Position.Deck.price F d j) : ticket w i j=0:=by
 let e:= RG10.Position.Deck.price F d i; have hv:e<d:=he.trans_le ( RG10.Position.Deck.price_bound .. )
 let a:= Pert.Position.lower F e d; have hz: (a: Set E)= LinearMap.range (RG10.Position.higher F hv.le):=by rw [ RG10.Gazebo.staircase ]; exact ( stairs_eq .. ).symm
 let Tp (q: RG10.Position.Deck F e):= RG10.Position.Deck.climb F hv.le q
 have hh(k:RG10.Position.Deck F e): RG10.Position.higher F hv.le (deck F e k)= deck F d (Tp k):= cabin ..
 have hx: w.val (K i)∈ LinearMap.range (RG10.Position.higher F hv.le):= by
    rw [show LinearMap.range _= _ from (?_ : LinearMap.range (RG10.Position.higher F hv.le)=a ) ]; swap; · exact SetLike.coe_injective hz.symm
    apply w.property.2.1 e hv; change deck F d i∈ ((a: Set E)); rw [hz]; obtain ⟨k,hk⟩:= RG10.Position.Deck.of_price F hv.le (j:=i) le_rfl; let q:=deck F e k; exact ⟨q,hk ▸ hh k⟩ -- orientation hack? `hk ▸`
 obtain ⟨u,h⟩:=hx
 apply Complex.ofReal_eq_zero.mp; rw [ticket_r,← h,← (deck F e).sum_repr u, map_sum, map_sum, Finsupp.finsetSum_apply]; apply Finset.sum_eq_zero; intro k _; rw [ map_smul, map_smul, hh k, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_of_ne ?_,smul_zero ]; intro H; rw [H] at he; exact not_lt_of_ge ( Deck.price_climb F hv.le k|>.symm ▸ ( RG10.Position.Deck.price_bound F e k )) he
-- throw in if compiler.Genuine
lemma tic_valid : ticket w∈tents F d:=by
 refine ⟨⟨tic_lower w, fun s=>?_⟩,funext fun i=>?_⟩
 · let v:=ride F s.ortho d; change (hop (ticket w)).comp v=v.comp (hop (ticket w)); rw [tic_oper]; apply LinearMap.ext; intro y; simp only [ LinearMap.comp_apply,cmS_at ]; exact Eq.symm (w.property.2.2.2.1 s y)
 unfold ticket; rw [ ground, w.property.1,map_zero ];rfl
abbrev tic := (⟨ticket w,tic_valid w⟩: tents F d)
lemma honest : RG10.Gazebo.buf (tic w)=w:= by
 apply Subtype.ext; ext1 x; change hop (ticket w) x=w.val x; rw [tic_oper,cmS_at]
end YM.FVAAlt2.First.Tent
