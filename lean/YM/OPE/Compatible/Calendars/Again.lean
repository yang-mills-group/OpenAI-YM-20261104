import YM.OPE.Compatible.Calendars.World
import YM.OPE.Compatible.Assemblage.Fuse
import YM.OPE.Compatible.Trees.Test
/-!
# Put the improved calendar together with the actual hierarchy.

Does NOT require nor assert physical matching. Only cutoff price
at grouping/conversion. Used below for the estimates reducing the
polylog sharpening to renormalization inputs, not conversely.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Filter Lattice RG MergeProof Spec
open PhysicalNext.Repeat.Legato Bandage
open scoped Topology Classical
variable {G:Gauge} (C:Family G)
-- includes both Shares and grants
structure Allot where
    W : Bid.Worth
    r: ℕ→ℕ
    D : ∀ N p m : ℕ,m<N → GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)
    buy : Package C W r D
    blades : TicketReady C (renal C.path.levels) r D
    bottoms : Tendsto r atTop atTop
    fixed (i : ℕ): (C.path.levels.budget i).supportExponent=100
lemma again (h:G.Simple){b:ℝ}(hb:0<b)(f:Extraction.Order) : ∃ (C:Family G), C.path.levels.clock.kernel.penalty=b ∧ Nonempty (Allot C) ∧ C.Makes ∧ ∃ (g:Extraction.Order)(A:Table C.book), Services C (f.refine g) A ∧ Nonempty (Final C (f.refine g) A):=by
   obtain ⟨C,hB,hC,hM,hW,⟨W,r,D,A,T,Z,t⟩,H,hQ,hF⟩:= noel_token h hb
   obtain ⟨g,P,L,R,S,E,hA,s,hN⟩:= hF f
   obtain ⟨hs,hG⟩:= hQ (f.refine g) s.copies
   obtain ⟨M,I,hI,p⟩:=Acme.emanate (W:=E) H h hs hG s hA.clean.ready hA.clean.tilt
   exact ⟨C,hB,⟨⟨W,r,D,A,T,Z,t⟩⟩,hM,g,S,⟨hs,h,⟨_,_,_,A⟩,P,L,R,E,hA⟩,Acme.glistens hC hA.clean.ready hA.clean.tilt p⟩ -- issue elab
open Ribbons Ribbons.ManyCopies
namespace Allot
variable {C}(A : Allot C)
def β (C: Family G)(i:ℕ):= C.path.levels.clock.hatBeta i
def eras (i:ℕ):ℝ:= (A.blades).choose i
def ringTime:= ((A.blades.choose_spec 0).city).choose
lemma admits {i N p:ℕ}(hi:C.ref 0 ≤ i)(ht:i < N): Admits (A.D N p i ht) A.r (renal C.path.levels i) (A.ringTime i) (A.eras i):=by
    have h:= (A.blades.choose_spec 0).city.choose_spec; exact ⟨h.suns i hi,(h.moon N p i hi ht).1, (h.moon N p i hi ht).2⟩
lemma arcPars {i:ℕ}(hi:C.ref 0≤ i): ClusterPars C.path (renal C.path.levels) A.eras A.r i:=by
    have hb:=A.blades.choose_spec 0; exact ⟨hb.crisp i hi,hb.funs i hi,hb.bars i hi⟩
lemma redraw {d i N p:ℕ} (hi:C.ref d≤ i)(ht:i<N): Throws C.path N p i (A.D N p i ht) (Next.Foundations.hol G) (Next.Foundations.localSection G d) (β C (i+1)):= A.blades.choose_spec d|>.brings i hi N p ht |>.2
include A
lemma stock {N p i:ℕ}(hi:C.ref 0 < i)(ht:i ≤ N):MergeProof.Menu.Arsenal (C.path.rep N p i):=by
    cases i with
    | zero => omega
    | succ i=> exact (A.admits (N:=N) (p:=p) (i:=i) (by omega) (by omega)).range'.contact
end Allot
end YM.OPE
