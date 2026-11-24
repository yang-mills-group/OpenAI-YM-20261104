import YM.Qlocal.Versal.Twirl
import YM.Next.RANK.Coordinates
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Versal
open Function Filter Metric Lattice Laurent RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Repeat.Deck Repeat.Deck.Mint Greenbelt 
open Poll Pond MeasureTheory ProbabilityTheory Stellar Progress.DirectedRecipe RGComparison01 AllOrder AllOrder.Burn AllOrder.Till
open Quipu Quipu.Lasso Quipu.Sonnet Marker
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G: Gauge}{c f C F c' f': Side}{i j k n m r M D D':ℕ}{g t d:ℝ}
  {V:Type}[DecidableEq V]{R:Marker.Census V}
variable (S:Tale R G)(X:S.Decision)(s:Senses R) (hc:C.val=c.val*D) (o: V→Site f) (O:V→Site F)
set_option quotPrecheck false
variable {P:Patch}(h:f.val=c.val*P.L.val) (H:F.val=C.val*P.L.val)
local notation "hF"=> Deck.fineP h H hc
local notation "q"=> Sonnet.root s
local notation "P0"=>o q
local notation "H'"=>decreed H
local notation "h'"=>decreed h
local notation "UK"=> Macrame.splitter (Deck.divides (Deck.fineP h H hc))
local notation "Σ!"=> Macrame.splitter (Deck.divides hc)
open Macrame Slide Deck

structure Marines (C f:Side) (V:Type) (o:V→Site f) where
   there : Site C
namespace Marines
-- common lift from ANY high deck centre. `Pose` used by Section.Knot.G algebra. retains all positions. only assumed close on s.Firsts stamp.ALL.
noncomputable def scale (x:Site C) (l:Site f): Site F:= (H').assemble (Deck.rise (Deck.divides hc) x ((h').parent l), (h').residue l)
lemma enrol (x:Site C)(l:Site f) : (decreed H).parent (scale hc h H x l)= Deck.rise (Deck.divides hc) x ((decreed h).parent l) := Ratio.assemble_parent .. -- order ? implicit s o
lemma landing (he:2≤c.val)(x:Site C)(l:Site f): (Macrame.splitter (Deck.divides (Deck.fineP h H hc))) (scale hc h H x l)=l:= by
 let ht:= Lace.project (h:=h) (H:=H) hc he; let t:=Deck.rise (Deck.divides hc) x ((decreed h).parent l); let w:=(h').residue l; exact (ht.regions t w).trans (Eq.trans (congr_arg (fun i:Site c=> (decreed h).assemble (i,w)) (Deck.dawns (Deck.divides hc) x ((decreed h).parent l))) ((h').unpack_at l))
-- general coherence data.
local notation "Y"=> O q
local notation "J"=> (decreed H).parent Y
local notation "Y'"=>(decreed h).parent P0
local notation "Q"=> Macrame.normal (Deck.divides hc) hc
structure Flank (s:Senses R)(x:Site C) (M:ℕ): Prop where
   ties : (decreed H).parent (O (Sonnet.root s))=x
   sailing (i:V) (hi:i∈ essence s): (o i)= (Macrame.splitter (Deck.divides (Deck.fineP h H hc))) (O i)
   fits(i:V) (hi:i∈ essence s): separation x ((decreed H).parent (O i)) ≤ M

section
variable (x:Site C)
include x
lemma forms (hh: (decreed h).parent (o (Sonnet.root s))=(Macrame.splitter (Deck.divides hc)) x) (hm: Tale.Live ((decreed h).parent ∘ o) s M) (he:2≤ c.val) : Flank (P:=P) hc o (scale hc h H x ∘ o) h H s x M:=by
 have ht:2*separation x x < c.val:=by rw [separation_self,mul_zero]; exact c.pos
 refine ⟨(enrol ..).trans ?_,fun i hi=>(landing hc h H he x (o i)).symm,fun i hi=> ?_⟩; · rw [hh]; exact boost (Deck.divides hc) x x ht
 rw [Function.comp_apply,enrol,Deck.climb, ← hh]; exact hm i hi
-- witness always choose one (or root exactly x for mask). Need phase orientation cost.
variable (F0: Flank hc o O h H s x M)
local notation "ℓ"=> P.L.val
abbrev border (R:Patch)(M:ℕ):= R.L.val * (2*M+2)
include F0
lemma phase (he:2≤c.val) (i:V) (hi: i∈essence s) : (decreed H).residue (O i)=(decreed h).residue (o i) ∧ (decreed h).parent (o i)=(Σ!) ((decreed H).parent (O i)) := by rw [F0.sailing i hi]; let L:= Lace.project (h:=h) (H:=H) hc he; exact ⟨(L.room _).symm, Lace.position L (O i)⟩
lemma respect (he:2≤c.val): (decreed h).parent (o (Sonnet.root s))= (Σ!) x := by rw [←F0.ties]; exact (Marines.phase s hc o O h H x F0 he _ (ownership s)).2
lemma helmet : Tale.Live ((decreed H).parent ∘ O) s M:= fun i hi=> (by show separation ((decreed H).parent (O q)) ((decreed H).parent (O i))≤ M; rw [F0.ties]; exact F0.fits i hi) -- dependent rewrite may touches O?
lemma pen (e:Senses R)(hx:essence e⊆ essence s) : Tale.Live O e (Marines.border P M):= by
 intro i hi
 let v:=Sonnet.root e; let a:= (decreed H).parent (O v); let b:= (decreed H).parent (O i); have hg: separation a b≤ 2*M:= le_trans (separation_triangle a x b) (by have he:=F0.fits i (hx hi); have hh:=F0.fits _ (hx (ownership e)); rw [separation_comm a x]; dsimp [v,a,b]; omega)
 let d:= (decreed H).embed a; let f:= (decreed H).embed b; have H1 : separation (O v) d ≤ ℓ := by have hz:2*separation (O v) d≤ℓ:= Corona.near (H') (O v); omega
 have H2 : separation (O i) f ≤ ℓ := by have hz:2*separation (O i) f≤ℓ:= Corona.near (H') (O i); omega
 have H3 : separation d f≤ P.L.val*(2*M) := (Next.Rank.Station.both (decreed H) a b).trans_le (Nat.mul_le_mul_left _ hg); have h1:= separation_triangle (O v) d (O i); have h2:= separation_triangle d f (O i); unfold border; change separation (O v) (O i)≤ ℓ*_; rw [separation_comm f] at h2; rw [Nat.mul_add]; omega
end
end Marines
end YM.Qlocal.Versal
