import YM.Integration.WilsonTrueProjectedDualHistory
import YM.Extra.SOURCE_HISTORIES.Pencil

/-! The true signed equation itself provides a representable germ at the
receiving date, even when no separate canonical address book for the
independently computed group field has been submitted. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedGermIncome
open Function Filter Finset MeasureTheory Lattice Wilson RG Labels Source
open Trace.Physical Trace.Physical.GermGraph
open Extra.Histories Extra.Histories.Relay Bid MergeProof
open PhysicalNext Repeat Legato Graces Roost Org QuadraticLocal QuadraticLocal.Advent
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonTrueProjectedColumnDescent WilsonTrueProjectedDualHistory
open scoped Topology Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {d N p i : ℕ}
local notation "Q" => GermGraph.store C d p
local notation "V" => GermGraph.value (C:=C) d N p
local notation "Y" => GermGraph.calValues (C:=C) d N p
local notation "π" => GermGraph.page (C:=C) d p
local notation "U" => GermGraph.transition (C:=C) d N p i

def Realizes (d N p i : ℕ) (f : Config G (C.side i p) → ℂ) : Prop :=
  ∃ (a : GermGraph.store C d p i) (r : ℝ), reads d N p i a r ∧
    f =ᶠ[𝓝 1] GermGraph.value (C:=C) d N p i a

theorem word {a : Q i} {r : ℝ} (h : reads d N p i a r) : Realizes d N p i (V i a) :=
  ⟨a,r,h,Filter.EventuallyEq.rfl⟩

theorem column (H : C.Makes) (opened : C.ref d ≤ i) (before : i ≤ N) (v : C.label d) :
    Realizes d N p i (Y i v) := word (entryOk d N p i H opened before v)

theorem add (H : C.Makes) (before : i ≤ N) {f g : Config G (C.side i p) → ℂ}
    (hf : Realizes (C:=C) d N p i f) (hg : Realizes (C:=C) d N p i g) :
    Realizes (C:=C) d N p i (f+g) := by
  obtain ⟨a,r,ha,af⟩ := hf
  obtain ⟨b,t,hb,bg⟩ := hg
  refine ⟨beside a b,r+t,presentation ha.1 ha.2 hb.1 hb.2,?_⟩
  have sum : V i (beside a b) = V i a + V i b := plus (H.wilson.represents N p i before).good
    ha.2 hb.2 (C.localSection d)
  rw [sum]
  exact af.add bg

theorem neg {f : Config G (C.side i p) → ℂ} (h : Realizes (C:=C) d N p i f) :
    Realizes (C:=C) d N p i (-f) := by
  obtain ⟨a,r,ha,af⟩ := h
  refine ⟨stretch (-1) a,_,⟨stretch_format _ ha.1,stretch_rem _ ha.2⟩,?_⟩
  have valueNeg : V i (stretch (-1) a) = -(V i a) := by
    funext B
    change (stretch (-1) a).density 0 (C.localSection d) (C.path.rep N p i) B = -_
    rw [stretch_density]
    simp
  rw [valueNeg]
  exact af.neg

theorem on_course (R : Run G) {m k : ℕ} (π₀ : ℕ → Layout G) (Γ : ℕ → Pace.Coin)
    (Ψ : ∀ j, RG.Rep G (R.family.side j p)) (course : Concourse R.alloy R.kit R.T π₀ Γ m N p k Ψ)
    (start : m ≤ i) (hi : i < N) (hc : Opened R.family d i p)
    {γ ε : ℝ} (gate : Gate R.family d N p i γ ε)
    (F : Spaces R p) {b t bound : ℝ} (v : R.family.label d)
    (upper : Full R (d:=d) (N:=N) Ψ F (i+1) v bound)
    (fresh : WilsonTrueProjectedDualHistory.Signed R (d:=d) (N:=N) Ψ F i b)
    (old : HardReturn R (d:=d) (N:=N) Ψ i t) : Realizes (C:=R.family) d N p i (F i) := by
  obtain ⟨q,h,r,B,paid,pn,hpaid,_,inlet⟩ := upper
  obtain ⟨e,book,_,fstep⟩ := fresh
  obtain ⟨z,u,oldBook,_,hstep,_⟩ := old h B hpaid
  obtain ⟨a,y,ap,_,_,pushQ⟩ := gate.2 q r paid pn
  let C := R.family
  have hV := word ap
  have fold : Realizes (C:=C) d N p i (GermGraph.transition (C:=C) d N p i
      (GermGraph.value (C:=C) d N p (i+1) q)) := by
    rw [pushQ]
    exact add R.makes hi.le hV (column R.makes hc.post hi.le y)
  obtain ⟨point,owners,_⟩ := WilsonMeasuredCourseQuietSlots.selected R π₀ Γ Ψ course start hi.le
  have quiet := (course.1.walk i start hi.le).view
  have landed (a : GermGraph.store C d p i) (price : ℝ) (hp : Admitted R Ψ i a price) :
      Realizes (C:=C) d N p i (a.density 0 (C.localSection d) (Ψ i)) := by
    obtain ⟨fmt,fee,hval,_⟩ := WilsonMeasuredOnlyHard.original a (C.path.rep N p i) (Ψ i) point
      quiet owners (C.localSection d) C.params 0 (safety C i) price hp.1 hp.2
    refine ⟨soft a,price,⟨fmt,fee⟩,?_⟩
    have clear := WilsonTrueProjectedTwoCarrierStep.clear (C:=C) (Ψ i) a hp.1
    filter_upwards [clear] with W hW
    rw [hval]
    rw [hW,Pi.zero_apply,add_zero]
  have qi := message d N p (i+1) R.makes (hc.post.trans i.le_succ) hi paid
  have yi := message d N p (i+1) R.makes (hc.post.trans i.le_succ) hi
    (entryOk d N p (i+1) R.makes (hc.post.trans i.le_succ) hi v)
  have aq := WilsonMeasuredOwnerIntegrable.original R π₀ Γ Ψ course (start.trans i.le_succ) hi
    (C.localSection d) C.params 0 h hpaid.1 hpaid.2
  have input : GermGraph.calValues (C:=C) d N p (i+1) v = F (i+1) +
      (GermGraph.value (C:=C) d N p (i+1) q + account h (Ψ (i+1))) := by rw [inlet]; abel
  have fi : Integrable (F (i+1)) (prior G _) := by
    rw [show F (i+1) = GermGraph.calValues (C:=C) d N p (i+1) v -
      (GermGraph.value (C:=C) d N p (i+1) q + account h (Ψ (i+1))) by rw [input]; abel]
    exact yi.sub (qi.add aq)
  have field := (factory_eq d N p i R.makes hc.post hi v).trans
    (congrArg (GermGraph.transition (C:=C) d N p i) input)
  change GermGraph.calValues (C:=C) d N p i v = GermGraph.transition (C:=C) d N p i
    (F (i+1)+(GermGraph.value (C:=C) d N p (i+1) q+account h (Ψ (i+1)))) at field
  have qreturn := (transition_add (C:=C) (i:=i) d N p qi aq).trans
    (congrArg (fun f => GermGraph.transition (C:=C) d N p i (GermGraph.value (C:=C) d N p (i+1) q)+f) hstep)
  have landedEq := (field.trans (transition_add (C:=C) (i:=i) d N p fi (qi.add aq))).trans
    (congrArg₂ (·+·) fstep qreturn)
  have out : F i = GermGraph.calValues (C:=C) d N p i v + -(
      (e.density 0 (C.localSection d) (Ψ i) +
       GermGraph.transition (C:=C) d N p i (GermGraph.value (C:=C) d N p (i+1) q)) +
       z.density 0 (C.localSection d) (Ψ i)) := by rw [landedEq]; abel
  rw [out]
  exact add R.makes hi.le (column R.makes hc.post hi.le v)
    (neg (add R.makes hi.le (add R.makes hi.le (landed e b book) fold) (landed z u oldBook)))

end YM.Integration.WilsonTrueProjectedGermIncome
