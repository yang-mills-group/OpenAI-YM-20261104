import YangMills.WilsonProof.NativeSupport.YM.MS.Graphical.Panels
import YM.Integration.FVA1Physical.Exchange.CalibratedExpansionCommonCalibratedGates

/-!
# The calibrated ContinuumLimit panels from the continuum integrals

Unconnected readings. The formal comparison between continuum
`Reg.State.wall` and Wilson `FrameConj.Gates.Thaw` in the library is an
internal calibrated equality. Use the
MS-bar integrals and counterterms in this directory from the *given* local
book `OpenAxis.Plot` and gauge group. The fitted position
frame too uses the *graph* reports (`measurablePanels`). This yields the same
`wall` and so also `Thaw`. This works on any initialization/store and finite
field horizon, with no resetting of the evanescent axes for each graph.
For applications directly to the Wilson prescription (graphs using `JRad.book`
in that horizon/labels convention), see further client files.
-/

noncomputable section
set_option autoImplicit false
namespace YM.MS.Graphical
open Function Filter Set MeasureTheory
open XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1
open FVA2 FVA2.Position FVA2.Position.OpenAxis FVA2.Arrival FVA2.Arrival.Schedule FVA2.Dframe WilsonMS
open Local.Physical Land Book Book.Program Book.Convolve Integration.FVA1Physical.Exchange
open scoped Topology Classical BigOperators

variable {G : Gauge} {n d k : ℕ} {x : Points n} {t : Test n}
variable (y : ℝ) (W : Initialize G) (V : Store G)
local notation "O" => Plot (Press.portDeck G)

/-- When closing named rows onto a general vector of physical fields, use the
fixed-frame coordinates with cumulative horizon (as in the MS specification).
A linear evaluator on arbitrary words needn't implement the row fit. -/
def separatedGraphSum (y : ℝ) (G : Gauge) (d : ℕ) (x : Points n) (k : ℕ) : Point G d n :=
  ∑ i: Fin n→ Toon G d, fullGraph (Plot (Press.portDeck G)) (Dframe.flash ∘ i) y
       (Arrival.Schedule.plot x) Finset.univ k • each i

lemma identification_screen (T : MS_Data G (Plot (Press.portDeck G))) (hx : x∈conf n) :
    separatedGraphSum y G d x k=meteor y T d x k := by
  unfold separatedGraphSum meteor; apply Finset.sum_congr rfl; intro i _
  rw [(identification _ _ y T (track hx)).2]; rfl

lemma raw_continuum : Reg.CoverTest.Continuum fun x:Points n=> separatedGraphSum y G d x k:= by
  obtain ⟨T⟩:= Land.bookedMS (G:=G) (Plot (Press.portDeck G))
  intro p; exact (Reg.CoverTest.measurable y T k p).congr (fun x hx=> congr_arg (fun M:Point G d n=> M p) (identification_screen y T hx))
/-- Fit on graph *test* values, not a continuum `MS_Data`. -/
def measurablePanels (y : ℝ) (G : Gauge) (d : ℕ) : Reports G d := fun k n=>
   Reg.CoverTest.cone (fun x:Points n=> separatedGraphSum y G d x k) (raw_continuum y)

def changes (y : ℝ) (V : Store G) (d : ℕ) : Guard G d := deck ((V.survey d).Lays (V.prepared d) (measurablePanels y G d))
def plotted (x : Points n) (d : ℕ): ℕ→ Point G d n := status (changes y V d) (separatedGraphSum y G d x)
def charted (d : ℕ) : Reports G d := realm (changes y V d) (measurablePanels y G d)

variable (T : MS_Data G (Plot (Press.portDeck G))) (F : MS_Data G (JRad.book G)) (h : G.Simple)
lemma predictions : measurablePanels y G d=Reg.State.kernel y T d := by
  funext k n; ext1 t; ext1 p; exact Test.apply_eq t (fun x hx=> congr_arg (fun M: Point G d n=> M p) (identification_screen y T hx))
lemma charts_guard : changes y V d = Reg.State.chooseL y V T d := by unfold changes Reg.State.chooseL; rw [predictions y T]

lemma applied_wall (hx : x∈conf n) : plotted y V x d=Reg.State.wall y V T d x := by
  unfold plotted Reg.State.wall; rw [charts_guard y V T,show separatedGraphSum y G d x = meteor y T d x from funext fun _=> identification_screen y T hx]
lemma applied_author : charted y V d=Reg.State.author y V T d:= by unfold charted; rw [charts_guard y V T,predictions y T]
lemma real_price (p : Tags G d n) : charted y V d k n t p=t.applyTo (fun x=>plotted y V x d k p):= by
  obtain ⟨T⟩:= Land.bookedMS (G:=G) O
  rw [applied_author y V T,Reg.State.exact_trace]; exact Test.apply_eq _ fun x hx=> by rw [applied_wall y V T hx]

include W h
/-- Independent MS-bar forest calculation of the two calibrated gates for any
`W V`, horizon and perturbative order on the indicated MS data.
Names/calibration `CalibratedExpansion.original_filed_calibrated_gates`.
Product formula in `Panels` can use a common IR cutoff across orders;
`Scoreboard` further justifies UV removal with common-cut graphs for these orders.
Uses the lookup/optics of `O=Plot` as in the input constructor.
-/
theorem calibrated_gates (x : Points n) (hx : x∈conf n) :
    plotted y V x d=Reg.State.wall y V T d x ∧ plotted y V x d=FrameConj.Gates.Thaw V F y d x:= by
  refine ⟨applied_wall y V T hx,?_⟩; rw [applied_wall y V T hx]; funext k; ext1 v; exact
      CalibratedExpansion.original_filed_calibrated_gates W T F h y V n d k v x hx

theorem calibrated_reports (d : ℕ) : charted y V d=Reg.State.author y V T d ∧
    charted y V d=FrameConj.Gates.thawed V F y d:=
  ⟨applied_author y V T,(applied_author y V T).trans (funext fun k=> CalibratedExpansion.original_filed_calibrated_reports W T F h y V d k)⟩

theorem cubic_normalization (P : Rose.Pick V) :
    (Rose.test P).applyTo (fun x=> plotted y V x 6 1 (Rose.tag G)) = (Rose.c_T P:ℂ) := by
  obtain ⟨T⟩:=Land.bookedMS O; obtain ⟨F⟩:= Land.bookedMS (JRad.book G)
  rw [← (CalibratedExpansion.original_first_triple_income W V P T F h y).1]; exact Test.apply_eq _ fun x hx=> by rw [applied_wall y V T hx]

-- Also compare `charted` and `plotted` with the readings along the supplied
-- X-space regulation after the indicated field/coupling changes. Uses
-- `Reg.State.moveR` and `.moveT`. This is **in the sense of `Reg.Higher.HasAll`
-- and `Senses`** (limits on Front and Gate filters, respectively), not an
-- identification with a finite mesh reading. Common finite-prescription choices.
include T F

theorem cost_at_regulator : ∃ (S : Prescription (Press.portDeck G))
    (A : Prescription (Ensure.deck G)), TaylorOKF T (Press.wickInput W) S ∧
    Favors.Horder S ∧ Ace.UnitP S ∧ BMenu.Installed W F A ∧ Rider.Commuting A ∧ S.team=A.team ∧
    ∀ (y:ℝ) (V:Store G) (d:ℕ), Reg.Higher.HasAll Front
        (fun i=> substitute (Dframe.reset y S i) (V.opens W i d)) (charted y V d) ∧
        ∀ (n k:ℕ) (v: Tags G d n),
          Senses (conf n) (fun i:Sample n=> substitute (FrameConj.pι A y i.F) (Rose.cooked W V d i) k v)
                 (fun x=> plotted y V x d k v) := by
  obtain ⟨A,hc,ha⟩ := Rider.Equipped W F h
  obtain ⟨S,ht,hs⟩ := continuumLimit_fund_team W T h A.team (by rw [← continuumLimit_ms_bulk F T]; exact ha.bulk)
  refine ⟨ S,A,hs.Taylor,hs.still,hs.base,ha,hc,ht,fun y V d=>?_ ⟩
  rw [applied_author y V T]; refine ⟨Reg.State.moveR y W V S T h hs.Taylor hs.still hs.base,?_⟩
  intro n k v x hx; dsimp only; rw [applied_wall y V T hx]; apply (Reg.State.moveT y W V S T h hs.Taylor hs.still hs.base v k x hx).congr'
  filter_upwards [(liftG x).eventually (continuumLimit_reset y S A ht)] with i hi; rw [hi]
end YM.MS.Graphical
