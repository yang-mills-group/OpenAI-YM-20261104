import YM.MS.ScaleForest.ListsPinned
/-!
# All ordered families with any NUMBER of marks

Data for graph construction. Marks tagged by the history carrying them and
specification of the position gaps. Can index by specific occurrences or
sum across occurrences using list sums. This level adds contractions only AFTER
separate bulk/single-port forests are taken into account (with ≥ two marks in the *result*),
not the bulk or single-
port evolution a second time. Spell out both the direct renormalized forest
(with prepared proper subgraphs), and the sum over polar substitution terms
at every nested level; prove its analytic and projection laws for arbitrary
participating labels, numbers of marks and projectors.

We always work on the open position stratum, realized later by the actual
separated tables, NOT contact distributions there. `Stand` records geometry
hypotheses for the proof. The multiplicities of every Feynman integrand are
Palette half-line ones of `ScaleForest`. This is a sector decomposition
prescription (not trying to match a different one per term). With ≥two pins
present, the parent measure, when momentum must be integrated, is that of
`WirePinned` (or `closeG`, respectively when joining two placed fields, or
adding an extra loop). Use `startPaid` unaltered also on maximal single-port
and bulk subgraphs, including the local pole terms
as well as when using renormalized results. This will be proved
analytically compatible with the operations at ≥two marks. `μ` consistently the REAL logarithmic
mass argument.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect Tone Momentum Osc Fiddle Metric
open scoped Topology ContDiff

/-- False: only one pin. True: at least two. -/
inductive Planted (G : Gauge) (I : Type) : Bool→Type where
| bed {h : ℕ} : GraphSum G false h → Planted G I false
| U : LineRule G → Planted G I true → Planted G I true
| B : LineRule G → GraphSum G true 4 → Planted G I true → Planted G I true
| P {b c : Bool} : LineRule G → (I → QP) → Planted G I b → Planted G I c → Planted G I true
namespace Planted
variable {G : Gauge} {I : Type} {b c : Bool} {h n : ℕ}

def pins : {b : Bool} → Planted G I b → ℕ
 | _, bed _ => 1
 | _, U _ p => p.pins
 | _, B _ _ p => p.pins
 | _, P _ _ p q => p.pins+q.pins

def slots : {b : Bool} → Planted G I b → ℤ
 | _, bed X => X.slots
 | _, U _ X=> X.slots-2
 | _, B _ X Y=> X.slots+Y.slots-2
 | _, P _ _ X Y=> X.slots+Y.slots-2

def resolve (μ:ℝ) : {b : Bool} → Planted G I b → Curtain G I
 | _, @bed _ _ h X => asLeaf X.instructions.renorm μ h
 | _, U K X => vertical (Ufor K μ (resolve μ X))
 | _, B K X Y => vertical (Bfor K (asLeaf X.instructions.renorm μ 0) (resolve μ Y))
 | _, P K A X Y=> vertical (Pfor K μ (resolve μ X) (resolve μ Y) A)

def push (μ:ℝ) : Planted G I true → Curtain G I
 | U K X => Ufor K μ (resolve μ X)
 | B K X Y=> Bfor K (asLeaf X.instructions.renorm μ 0) (resolve μ Y)
 | P K A X Y=> Pfor K μ (resolve μ X) (resolve μ Y) A

/-- Actual graph integral terms. Include all choices of polar forest readings
in children, k-loop indexed as in each contracted proper graph (in particular,
pole terms were integrated with complements at the current regulator). -/
def forests (μ:ℝ) : {b : Bool} → Planted G I b → List (Curtain G I)
 | _, @bed _ _ h X => X.quotients.map (startPaid μ h)
 | _, U K X=> ((forests μ X).map (Ufor K μ)).map vertical
 | _, B K X Y=> (expandsTwo (Bfor K) (X.quotients.map (startPaid μ 0)) (forests μ Y)).map vertical
 | _, P K A X Y=> (expandsTwo (fun X Y=> Pfor K μ X Y A) (forests μ X) (forests μ Y)).map vertical

def parts (μ:ℝ) : Planted G I true→ List (Curtain G I)
 | U K X=> (forests μ X).map (Ufor K μ)
 | B K X Y=> expandsTwo (Bfor K) (X.quotients.map (startPaid μ 0)) (forests μ Y)
 | P K A X Y=> expandsTwo (fun X Y=> Pfor K μ X Y A) (forests μ X) (forests μ Y)

lemma rooting (X:Planted G I true) (μ:ℝ) : resolve μ X = vertical (push μ X) := by cases X <;> rfl
lemma found (X:Planted G I true) (μ:ℝ) : forests μ X=(parts μ X).map vertical := by cases X <;> rfl

-- parameter admissibility for proofs
variable [TopologicalSpace I]

def Stand : {b:Bool} → Planted G I b → Prop
 | _, bed _ => True
 | _, U _ X=> X.Stand
 | _, B _ _ Y=> Y.Stand
 | _, P _ A X Y=> X.Stand ∧ Y.Stand ∧ AdmittedGap A

variable (μ:ℝ)

def active (F:Curtain G I) (p:ℤ)(b:Bool) : Prop:= (b=true→ MultiFuel F p) ∧ Paces F p ∧ Frontier F

theorem activated {F:Curtain G I}{p:ℤ}(h:MultiFuel F p)(ht:Frontier F): active F p true := ⟨ fun _=> h, paceFuel h,ht⟩
theorem inert {F:Curtain G I}{p:ℤ}(h:Paces F p)(ht:Frontier F): active F p false := ⟨fun r=>Bool.noConfusion r,h,ht⟩

private def Commited (μ:ℝ)(F:Planted G I b):Prop:= ∀ p:b=true, let X:Planted G I true:= p ▸ F; Crossing (push μ X) X.slots

variable [FirstCountableTopology I]
lemma Crossing.active {X:Curtain G I}{q:ℤ}(hp:Crossing X q): active (vertical X) q true:= activated (paidVertical hp) (Frontier.drivePast hp)

private lemma allObey (X:Planted G I b) (h:X.Stand): active (resolve μ X) X.slots b∧Commited μ X := by
   induction X with
   | bed X=> obtain ⟨hp,ht⟩:= occupancy (I:=I) X μ; exact ⟨inert ht hp,fun q=>Bool.noConfusion q⟩
   | U K X ih=> have H:= fueledU K μ ((ih h).1.1 rfl); exact ⟨ Crossing.active H,fun _=>H⟩
   | B K X Y ih=> have H:= fueledB K (resetBulk X μ) ((ih h).1.1 rfl); exact ⟨ Crossing.active H,fun _=>H⟩
   | P K A X Y ih it=> have H:= fueledP K μ h.2.2 ((ih h.1).1.2.1) ((it h.2.1).1.2.1); exact ⟨ Crossing.active H,fun _=>H⟩

theorem offers (X:Planted G I b) (h:X.Stand): active (resolve μ X) X.slots b := (allObey μ X h).1
theorem pushing (X:Planted G I true)(h:X.Stand): Crossing (push μ X) X.slots:= (allObey μ X h).2 rfl

end Planted
end YM.MS.ScaleForest
