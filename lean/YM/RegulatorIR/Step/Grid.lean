import YM.RegulatorIR.Diagram.Linear

/-!
Data for the *internal formal diagrams*. Use concrete decks at spacing λ
at each stage. Keeping them as parameters rather than tying block sizes to the
physical measuring schedule is intentional. The common regulator has its own
side divisions. `addon` is in log-sign convention, field-independent scalar
optional (computed modulo such constants). It must actually be supplied by
bulk recursion data and agree with Wilson primitives; not part of the
conclusion.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Step
open Budget Motion Budget.Deck Budget.Tariff Budget.Packet Budget.Layer Diagram Function
open scoped Topology ENNReal NNReal BigOperators Classical
variable {X Y U V: Type} {P:ℝ} (A:Deck P X U)(B:Deck P Y V)
def combine : Deck P (X⊕Y) (U⊕V) where
 pos:= Sum.elim A.pos B.pos
 orbit:= Sum.map A.orbit B.orbit
 place:= Sum.map A.place B.place
 placed a:=by cases a <;> simp [A.placed,B.placed]
 wind d:= Equiv.sumCongr (A.wind d) (B.wind d)
 neutral x:= by cases x <;> simp [A.neutral,B.neutral]
 reversed d:= by rw [A.reversed,B.reversed]; rfl
 projected d a:= by cases a <;> simp [A.projected,B.projected]
 displaced d a:=by cases a <;> simp [A.displaced,B.displaced]
 edges a b:= by
    cases a <;> cases b <;> rename_i x y
    · intro h; simpa using A.edges x y (Sum.inl.inj h)
    · simp
    · simp
    intro h; simpa using B.edges x y (Sum.inr.inj h)
 orient:= Sum.elim A.orient B.orient
 north x:= by cases x <;> simp [A.north,B.north]
 retreat d x:= by cases x <;> simp [A.retreat,B.retreat]

def firstChannel: Channel A (combine A B) := ⟨Function.Embedding.inl,Function.Embedding.inl,fun _ _=>rfl,fun _=>rfl,fun _=>rfl,fun _=> rfl,fun _=> rfl⟩
def lastChannel: Channel B (combine A B) := ⟨Function.Embedding.inr,Function.Embedding.inr,fun _ _=>rfl,fun _=>rfl,fun _=>rfl,fun _=> rfl,fun _=> rfl⟩

/-- Copies and contractions at this step. Zone coordinates are physical.
Weights and pre/post bounds supplied separately. This is a *formal* step
presentation. No Markov conditional law asserted merely from these fields. -/
structure GridStep (A:Deck P X U)(B:Deck P Y V) where
 line : Layer (X⊕Y) (X⊕Y)
 driftL : Layer (X⊕Y) (X⊕Y)
 addon : Orders (X⊕Y)
-- A B not used? parameter declare actually

namespace GridStep
variable {A:Deck P X U}{B:Deck P Y V}
variable (S:GridStep A B)

def jVac (T:Orders X): Orders (X⊕Y):=fun e r=> offer (firstChannel A B).native (T e r)+S.addon e r
def jOrb (F:Orders U): Orders (U⊕V):=fun e r=> offer (firstChannel A B).tile (F e r)+(combine A B).deckSum (S.addon e r)

def layer := wrapL (combine A B) (combine A B) S.line
def mean := wrapL (combine A B) (combine A B) S.driftL

def pullI {r:ℕ}(Z : Packet (X⊕Y) r):Packet Y r:= crop (lastChannel A B).native (draft S.driftL Z)
def pullJ {r:ℕ}(Z : Packet (U⊕V) r):Packet V r:= crop (lastChannel A B).tile (draft S.mean Z)

def pure (T:Orders X):Orders Y:=fun e r=> if r=0 then 0 else S.pullI (ceaseHeat S.line (S.jVac T) false e r)
def common (F:Orders U):Orders V:=fun e r=> if r=0 then 0 else S.pullJ (ceaseHeat S.layer (S.jOrb F) true e r)

def each (m:ℕ)(T W:Orders X):Orders Y := fun e r=> S.pullI (endHeat m S.line (logHeat S.line (S.jVac T) false) (fun e r=>offer (firstChannel A B).native (W e r)) e r)
def island (m:ℕ)(T W:Orders U):Orders V:=fun e r=> S.pullJ (endHeat m S.layer (logHeat S.layer (S.jOrb T) true) (fun e r=> offer (firstChannel A B).tile (W e r)) e r)
end GridStep
end YM.RegulatorIR.Step
