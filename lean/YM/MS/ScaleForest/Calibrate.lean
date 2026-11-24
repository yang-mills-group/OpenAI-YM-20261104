import YM.MS.ScaleForest.UnaryConvention
import YM.Integration.FVA1Physical.Exchange.CalibratedExpansionCommonFreePanel
import YM.Integration.FVA1Physical.Exchange.CalibratedExpansionCommonCalibratedGates
import YM.WilsonMS.Scales.EndComparison
/-!
# Calibrated finite coefficient identification

We now have GUARD and POINT independently computed from the actual
UV/IR readings. Thus reports, across all field grades (one convention),
including the position comparison from the question. Evaluates at the
*converted* fields, real tangent-power $g$ convention in the MS variable.

As always the real argument ν is **logarithmic**, the vertex clock in
`MeasureD` (measure exponent `exp(-2 z ν)`); at ν=0 measure has
`feeD` and at clock μ (the local `$μ$` often used earlier in ScaleForest)
it also has that exponential. Thus if quoting conventional mass use
ν=log(unit-mass-in-length^-1 sqrt ζ); it's ν, not that positive scale,
that is passed into `scaledResult` and all the invocation patterns below.

This computes precisely FIELD-converted coefficient (coupling already in
MS variable). We also call existing `Gate` / actual finite-survey
comparison (uses SAME shared team and coupling reset eventual on Front at
all arities); no removal assumptions supplied by us, this is using
original hypotheses for this constructor. No positive-coupling / numerical
true Wilson cutoff estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.Panels
open Function Filter Set MeasureTheory
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open Local.Physical Menus Land Book Book.Program Book.Convolve
open High High.Knobs Outlook Wind Wind.Leading Motif Mach Dock Hem
open Planted FVA2 FVA2.Position FVA2.Position.Axes FVA2.Arrival Dframe WilsonMS
open Normalize.Fray Integration.FVA1Physical.Exchange Integration.FVA1Physical.Exchange.CalibratedExpansion
open scoped Topology Classical BigOperators
variable {n d k : ℕ}{G:Gauge}
variable (P:Palette G) (ν:ℝ) (V:Store G)
local notation "O"=> OpenAxis.Plot (Press.portDeck G)
local notation "W"=> Fin n

/-- Compact name for reading with EXP of all planted history forests
connected parts. `priceBook` is using exactly the two ordered limits after
the full list's UV-cutoff forest terms. -/
def gross (Y:Fin n → Toon G d) (k:ℕ) (x:Points n):= byPartition (priceBook P ν (inducted O ∘ flash ∘ Y) (Schedule.plot x)) Finset.univ k

def stage (d:ℕ)(x:Points n) (k:ℕ) : Point G d n := ∑ a: Fin n→ Toon G d, gross P ν a k x • each a

variable (M : MS_Data G (OpenAxis.Plot (Press.portDeck G)))
variable (F : MS_Data G (JRad.book G))
lemma tracked (p:Points n)(hp:p∈conf n)(i:ℕ): stage P ν d p i=meteor ν M d p i:= by
   unfold stage meteor; apply Finset.sum_congr rfl; intro j _; unfold gross; rw [ point_income P ν M (flash∘j) (Schedule.track hp) ]; rfl
lemma continuous_stage (d k n:ℕ) : Reg.CoverTest.Continuum (fun x:Points n=> stage P ν d x k) := by intro v; exact (Reg.CoverTest.measurable ν (graph_data P O) k v).congr (fun i hi=> by dsimp only; rw [ tracked P ν (graph_data P O) i hi ])
def blots (d:ℕ) : Reports G d:= fun k n=> Reg.CoverTest.cone _ (continuous_stage P ν d k n)
lemma reports (d:ℕ) : blots P ν d=Reg.CoverTest.Rates ν M d:= by
    funext k n; ext1 t; ext1 v; exact Test.apply_eq _ (fun z hz=> by dsimp only; rw [tracked P ν M z hz])

def conversionG (d:ℕ) : Guard G d:= deck ((V.survey d).Lays (V.prepared d) (blots P ν d))

theorem reads_guard (d:ℕ) : conversionG P ν V d= Reg.State.chooseL ν V M d:= by unfold conversionG; rw [ reports P ν M ]; rfl
def scaledResult (d:ℕ)(x:Points n) (k:ℕ) : Point G d n:= status (conversionG P ν V d) (stage P ν d x) k
def priced (d k:ℕ) := realm (conversionG P ν V d) (blots P ν d) k

theorem conversionFormula (v:Tags G d n)(x:Points n) (k:ℕ) : scaledResult P ν V d x k v=
    ∑ a∈ tally k n,∑ t: Fin n → Toon G d, gross P ν t (a none) x * each t (pulseU a (conversionG P ν V d) v):= by rw [ scaledResult, seen ]; unfold stage; simp only [sum_apply,smul_apply]; rfl

theorem continuum_gated (d k:ℕ) {x:Points n}(hx:x∈conf n): scaledResult P ν V d x k= Reg.State.wall ν V M d x k:= by
    unfold Reg.State.wall scaledResult; rw [ reads_guard P ν V M, funext (tracked (d:=d) P ν M x hx ) ]

variable (Y:Initialize G) (h:G.Simple)
include h
-- expose calibrated endpoints as actual claims (hypotheses from filed theorem)
include Y M

theorem filed_gated {x:Points n}(hx:x∈conf n)(v:Tags G d n)(k:ℕ) : scaledResult P ν V d x k v= FrameConj.Gates.Thaw V F ν d x k v:= by rw [ continuum_gated P ν V M d k hx, original_filed_calibrated_gates Y M F h ν V n d k v x hx ]

omit h Y in
theorem dated (d k:ℕ) : priced P ν V d k= Reg.State.author ν V M d k:= by rw [ priced,reports P ν M, reads_guard P ν V M ]

theorem reports_filed (d k:ℕ) : priced P ν V d k= FrameConj.Gates.thawed V F ν d k:= by rw [ dated P ν V M, original_filed_calibrated_reports Y M F h ν V ]

omit h Y in
theorem reports_trace (x: Test n)(v: Tags G d n)(k:ℕ) : priced P ν V d k n x v= x.applyTo (fun p=> scaledResult P ν V d p k v):= by rw [ dated P ν V M, Reg.State.exact_trace ν V M ]; exact Test.apply_eq _ fun z hz=> congr_arg (fun i:Point G d n=> i v) (continuum_gated P ν V M d k hz).symm

omit h Y in
theorem free (v:ℝ) (d:ℕ) : (V.measure d).D (blots P ν d 0)=(V.measure d).D (VisitH.Continuum F v 0 d) := by rw [ reports P ν M]; exact original_free_panel M F ν v d V

include F in
theorem first (q:Rose.Pick V) : priced P ν V 6 1 3 (Rose.test q) (Rose.tag G)=(Rose.c_T q:ℂ):= by rw [dated P ν V M, Reg.State.exact_trace ν V M]; exact (original_first_triple_income Y V q M F h ν).1

omit h Y M in
/-- `Gate` is the filed FINITE problem. Here we pin that coupling
conversion too: one common team (the same one as on WilsonMS with F)
works simultaneously. Two sides at different field protocols can use
it. This isn't a new cutoff approximation. Ensures the independent
integrals are after that conversion (with the inverse mass-flow etc.
not secretly retuned by comparing *these* prices). -/
theorem coupled (Y:Initialize G)(T : MS_Data G (OpenAxis.Plot (Press.portDeck G)))
    (F : MS_Data G (JRad.book G)) (h:G.Simple) :
    ∃ (A:Prescription (Press.portDeck G)) (B:Prescription (Ensure.deck G)),
      A.team=B.team ∧ Ace.Sag Y T A ∧ Rider.Commuting B ∧ BMenu.Installed Y F B ∧
      ∀ (ν:ℝ) (V:Store G) (n d k:ℕ),
        (∀ v:Tags G d n,Senses (conf n) (fun i=> Program.substitute (FrameConj.pι B ν i.F) (Rose.cooked Y V d i) k v) (fun p=> scaledResult P ν V d p k v)) ∧
        ∀ (t:Test n)(v:Tags G d n),Tendsto (fun i=> Program.substitute (FrameConj.pι B ν i) (V.opens Y i d) k n t v) Front (𝓝 (priced P ν V d k n t v)):= by
   obtain ⟨A,hA,u⟩:= Rider.Equipped Y F h; obtain hb : Fixed (col (skyline G A.team)) (Archive 4 T.bulk) true 4 1:= by rw [← continuumLimit_ms_bulk F T]; exact u.bulk
   obtain ⟨S,hS,H⟩:=continuumLimit_fund_team Y T h A.team hb; refine ⟨ S,A,hS,H,hA,u,?_⟩; intro ν V n d k; have he:= continuumLimit_reset ν S A hS; constructor
   · intro v x hx; dsimp only; rw [ continuum_gated P ν V T d k hx ]; exact (Reg.State.moveT ν Y V S T h H.Taylor H.still H.base v k x hx).congr' ((liftG x).eventually he|>.mono fun i hi=> by dsimp only; rw [hi])
   · intro t v; rw [ dated P ν V T ]; exact (Reg.State.moveR (d:=d) ν Y V S T h H.Taylor H.still H.base k n t v).congr' (he.mono fun i hi=> by dsimp only; rw [hi])

omit h Y M
-- Apply the standard constructors (mathematical calculation, not machine numeric).
def stock (G:Gauge): MS_Data G (OpenAxis.Plot (Press.portDeck G)):= Classical.choice (bookedMS _)

theorem appointed (P:Palette G)(ν:ℝ)(V:Store G)(Y:Initialize G)(h:G.Simple)(n d k:ℕ)(x:Points n)(hx:x∈conf n) (v:Tags G d n):
    let U:= Network.continuum G; let M:= stock G;
    scaledResult P ν V d x k v=Reg.State.wall ν V M d x k v ∧
      scaledResult P ν V d x k v=FrameConj.Gates.Thaw V U ν d x k v ∧
      priced P ν V d k= FrameConj.Gates.thawed V U ν d k := by intro F M; exact ⟨ congr_arg (fun i:Point G d n=> i v) (continuum_gated P ν V M d k hx), filed_gated P ν V M F Y h hx v k, reports_filed P ν V M F Y h d k⟩
end YM.MS.ScaleForest.Panels
