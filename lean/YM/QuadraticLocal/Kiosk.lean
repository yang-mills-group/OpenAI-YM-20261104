import YM.QuadraticLocal.Canopy
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Marlin.Haul
/-!
Compact receipt witnessed by unmarked bootstrap. First certificate identifies EVERY input and
output K address of the particular unmarked `invested` call with the primitive vacuum merger
outputs. Second certificate includes extra slack to allow Mark-only mask change in this merge:
we'll carry the caller's polynomial exactly and pay it.

All sorts / χ / degrees passive. Output stakes preceding test arguments certify a deterministic
accompanying state on that same vacuum, including after choice of nonanalytic error labels still.
Users of group/teststenciling use these full witness states, not round trip arbitrary "same-density".
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Kiosk
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open RG3 RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe Payments Fusion Attached Canopy
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{p:BudgetPoint}{X:Pipes G n}{d:Tap G n}{x y e a b c f q:ℝ}{B:ℕ}
variable {U W:Activities G n}
-- Track layout and supports. certificates inspectable at every G & n; fork joins don't choose
-- intermediate stores separately on each t. Parameters e,f are incoming & outgoing hard hit prices.
-- OffRoom second certificate incl r (extra soft movement allotment).
structure First (p:BudgetPoint) (U W:Activities G n)(e f a:ℝ) where
   skeleton : Pipes G n
   tap : Tap G n
   roll : ℕ≃ skeleton.Pellet
   oldP : U.forced = skeleton.kernel
   oldV : U.K= tap.forced
   projection : W.forced = addr roll p
   keeps : W.K= solid roll p tap
   mainly : ℝ
   score : ℝ
   softens : Hard.Soft skeleton tap p
   softPaid : Hard.SoftPrice skeleton tap p.B (a+1) mainly
   funds : Rates p.B f e mainly score
-- a = output exponent. (input exponent = a+1)
structure Second (p:BudgetPoint)(U W:Activities G n)(e f a r:ℝ) where
   skeleton : Pipes G n
   tap : Tap G n
   oldP : U.forced= skeleton.kernel
   oldV : U.K=tap.forced
   projection : W.forced = addr (folio G n) p
   keeps : W.K= solid (folio G n) p (Rack.widen skeleton tap)
   mainly : ℝ
   score : ℝ
   softens : Hard.Soft skeleton tap p
   softPaid : Hard.SoftPrice skeleton tap p.B (a+1) mainly
   funds : Rates p.B f e (mainly+r) score
section transfers
variable {V : Type}[DecidableEq V]{R:Census V}{o:V→Site n}{T ι:Type*}{w:V→ℝ}

def shape {P Q:ℕ→ ForcedAddress G n}{F W: Code G n} (hP:P=Q)(hF:F=W) (L:Hard T p P F o R): Hard T p Q W o R:=
   ⟨L.hard,hP ▸ L.locality,hP ▸ L.charged, fun t i U=> by rw [L.quiet, hF]⟩ -- due to L.hard type? rewrites
variable {U' W' : Activities G n}
lemma turned {P Q:ℕ→ ForcedAddress G n}{F W: Code G n}(hP:P=Q)(hF:F=W)(L:Hard T p P F o R)(h:L.Paid w B a e) : (Kiosk.shape hP hF L).Paid w B a e:=by subst F P; exact h
variable [Fintype V]
variable (S L:T→ Config G n→ Poly R)
lemma pivot (hP:U.forced=W.forced)(hV:U.K=W.K) (Z:Hard T p U.forced U.K o R) (h:ReadZone T p U Z S L): ReadZone T p W (Kiosk.shape hP hV Z) S L:=by
   have hh t A: (packet W p (Z.hard t) A)=(packet U p (Z.hard t) A):=by funext i; unfold packet; rw [show U.admissible p A i=W.admissible p A i from (by unfold Activities.admissible; rw [hP])]
   intro t U'; simpa only [Kiosk.shape,hh t U'] using h t U'
variable (H:Hard T p U.forced U.K o R)
namespace First
variable (D:First p U W e f a)
def led : Hard T p W.forced W.K o R:= Kiosk.shape D.projection.symm D.keeps.symm ((Kiosk.shape D.oldP D.oldV H).transport D.roll D.softens)
lemma passes (hw:∀ i,0<w i)(hb:H.Paid w p.B (a+1) e)(ha:0≤a)(hZ:ReadZone T p U H S L): (First.led H D).Paid w p.B a f∧ReadZone T p W (First.led H D) S L:=by
    let L0:= D.skeleton; let g:= (bridge S L D.roll (Kiosk.shape D.oldP D.oldV H) D.softens (turned _ _ H hb) D.softPaid D.funds hw ha (pivot S L (U:=U) (W:=L0.pours D.tap) D.oldP D.oldV H hZ)); exact ⟨turned _ _ _ g.1,pivot S L (U:=fused D.roll p D.tap) D.projection.symm D.keeps.symm _ g.2⟩
end First
namespace Second
variable [Countable ι]
variable (M:ShiftRows T ι G p o R)
variable (D:Second p U W e f a c)
def canopy : Hard T p W.forced W.K o R:= Kiosk.shape D.projection.symm D.keeps.symm (M.poster D.softens (Kiosk.shape D.oldP D.oldV H))
lemma passes (hw:∀ i,0<w i)(ha:0≤a)(hT:H.Paid w p.B (a+1) e)(hx:M.Budget w p.B (a+1) c)(hZ:ReadZone T p U H S L)
     (log:T → Config G n→ Poly R)
     (h:∀ t O,L t O=log t O+M.log t O)(hp: ∀ t O,(log t O).part R.quiet=0): (Second.canopy H M D).Paid w p.B a f∧ReadZone T p W (Second.canopy H M D) S log:=
   ⟨turned D.projection.symm D.keeps.symm _ (M.budgets D.softens (Kiosk.shape D.oldP D.oldV H) hw ha D.softPaid (turned _ _ H hT) hx D.funds), pivot S log (U:=fused (folio G n) p _) D.projection.symm D.keeps.symm _ (M.light_shade D.softens (Kiosk.shape D.oldP D.oldV H) hw ha D.softPaid (turned _ _ H hT) hx D.funds S L log (pivot S L (U:=U) (W:=D.skeleton.pours D.tap) D.oldP D.oldV _ hZ) h hp)⟩
end Second
end transfers
-- instantiate once on the inserted dictionary before α tests. Primary support threshold p.
section marlin
open PhysicalNext PhysicalNext.Repeat AnalyticBridge.VerifiedReset Marlin Collection Animals
variable (P' : Listing G n)(z s:ℕ)(A: Collection.Source G n) (k t: Trio.Offer G n)
variable (h:∀ i, Trio.Tidy p (neighbors s i) (t i))(ht:∀ i U,t i U≠0→¬Healthy p.threshold (neighbors s i) U)
local notation "d"=> bison A k t
local notation "L"=> lodge P' z s
local notation "q"=> (p.supportExponent+1)
include h ht in
lemma sheath : Hard.Soft L d p:=⟨fun i=>(estateP P' z s A k t h i).invariant,fun i=>(estateP P' z s A k t h i).uses,fun i=>(estateP P' z s A k t h i).borel,failedP P' z s A k t ht⟩ -- include
variable (hv:∀ i V, ‖t i V‖≤ a)(he:∀ i:Site n,(coverNumber p.B (neighbors s i):ℝ) ≤ b)
include h ht hv he
lemma launch (hR:Rates p.B f e (tithe s a p b) y): Nonempty (First p (P'.read A) ((pluck p L).read (poursP p L d)) e f q) := by
   have ha:0≤a:= (norm_nonneg _).trans (hv 0 1); obtain ⟨hq,hG⟩:= Marlin.caps P' z s p a ha he
   exact ⟨L,d,hak _,rfl,rfl,rfl,rfl,_,_,sheath P' z s A k t h ht,⟨ _,hq,Marlin.softly A t a hv k,hG⟩,hR⟩
end marlin
end YM.QuadraticLocal.Kiosk
