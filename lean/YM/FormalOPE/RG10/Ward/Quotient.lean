import YM.FormalOPE.RG10.Ward.Valuations
import YM.FormalOPE.RG10.Ward.Longitudinal
import YM.FormalOPE.RG10.CommonStamps

/-!
# Physical (not ghost or off-shell external) EOM relations on finite stencil coefficients

Retain integer weights/coupling grades and use only under separated test supports. This is a
*working* quotient modulo the indicated Ward--EOM relations, not a completeness/rank theorem
(that, leading free-jet checks, pivot conversions and comparison to the actual `Table` quotient
in the continuum are separate obligations). Coefficient algebra accepts complex linear and
order-by-order changes, real EOM representatives. Include a `b∈ports` component for each
inversion-partner pair touched. Local X stencils (`Proxy` with `Direction.carrying`) as needed at
your kframe scales are allowed; the mathematical identity is broader, admits nonlocal ones too,
so long as **other** test supports miss the updating links for actually descending. Clear poles
BEFORE working in normalized columns.

The separated theorem allows changing the entire query capture by elements of that span when the
spectator aperture here and integrability and identity of representatives hold. Does not assert
a well-conditioned (nonredundant) basis at every scale, or that every separated-observationally
null stencil is in this span. Need the *same correction data* when taking limits, and use the
exported RHS of `contact_payment` (for **that** lift and **that** test) instead of feeding the
quotient to contact operations. The tests here live at fixed lattice regulator; nothing about
coincidence in continuum or infrared limit. Frame/stress/EOM photon quotient etc require further
estimates. `closedTower` below supplies minimal BRST closure with any number of insertions
(no arity one Ward endpoint assumed). Treat arbitrary covariance changes outside this minimal
invariant sublanguage separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.InversionWard
open Gauge Lattice RG Wilson MeasureTheory Metric Finset
open PertExtension PertExtension.Orb Function Filter InversionTop PowerSeries BRST
open YM.PertExtension.Series YM.PertExtension.Series.Radial YM.PertExtension.Series.Tested
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {n : Side} (hn : Even n.val) {I : Type*}
variable (ports : Set (Edge (Site n)))
local notation "S" => RG10.Series
local notation "F" => feed (G:=G) hn
local notation "W" => vertices G n
local notation "K" => Kernel (Unit × Dir G n)

/-- Raw lift; label before modding out. -/
structure Adjustment (G : Gauge) (n : Side) where
  e : Edge (Site n)
  X : Config G n → G.Color
  d : ℕ
  valid : Direction e X
  approved : Approved e X d

namespace Adjustment
variable (L : Adjustment G n)

def valued : Kernel (Unit × Dir G n) := equationMark L.d L.e L.X
def localTo (L : Adjustment G n) (s : Finset (Site n)) := LocalOn s L.X
-- no extension to the larger orbit implicit in this data
end Adjustment

variable (a b : Adjustment G n)
variable {v : Finset I} {σ : I → Stamp G n} (hv : ∀ i∈v, Proxy (σ i).stencil)

/-- Ambient EOM submodule for testing. Use its restriction to the represented `Word`/field
stencils when applicable. Only use this **under** observables with aperture proof. -/
def corrections (G : Gauge) (n : Side) (ports : Set (Edge (Site n))) : Submodule RG10.Series (Kernel (Unit × Dir G n)) :=
  Submodule.span RG10.Series {A | ∃ L : Adjustment G n, L.e∈ports ∧ A=L.valued}
local notation "P_" => corrections G n

lemma accounts (L : Adjustment G n) (h : L.e∈ports) : L.valued∈(P_ ports) := Submodule.subset_span ⟨L,h,rfl⟩

def spectators (v : Finset I) (σ : I → Stamp G n) := ∏ i∈v, (σ i).couplingMark

variable (f g : Kernel (Unit × Dir G n)) {ports}
local notation "tests" => spectators v σ

include hv
lemma paid_lift [DecidableEq I] : (F).Funded ((W).weight * (a.valued * tests)) :=
  (chartContact hn a.valid v a.approved hv).1
include hn

/-- Evaluation from genuine Ward data on a contact. -/
theorem contact_payment [DecidableEq I] :
    (F).step W (a.valued * tests) =
    lower (a.d+1+Stamp.degrees σ v) (X^2 * ∑ i∈v, replyCoeff (hitsAt σ v i a.e a.X)) := by
  have H := (chartContact hn a.valid v a.approved hv).2
  rw [← H,lower_delay]; rfl

theorem annihilator [DecidableEq I]
    (h : f∈corrections G n ports) (s : I → Set (Site n)) (hp : ∀ i∈v, LocalOn (s i) (σ i).stencil)
    (he : ∀ i∈v,∀ e∈ports, off e (s i)) :
    (F).Funded ((W).weight * (f * tests)) ∧ (F).step W (f * tests)=0 := by
  induction h using Submodule.span_induction with
  | mem a h =>
    obtain ⟨L,h,rfl⟩:=h
    exact ⟨paid_lift hn L hv,excluded hn L.valid v L.approved hv s hp (fun i hi => he i hi _ h)⟩
  | zero =>
    rw [zero_mul]; refine ⟨by rw [mul_zero]; exact FlatFeed.Funded.zero,?_⟩
    rw [FlatFeed.step,mul_zero]; rw [show (F).average 0=0 from ?_,zero_mul]
    apply PowerSeries.ext; intro k
    rw [FlatFeed.average_coeff, show row k 0 = (0: Unit × Dir G n→ℂ) from ?_, FlatFeed.mean_zero,map_zero];
    funext x; simp [row]
  | add a b _ _ ha hb =>
    rw [add_mul]
    exact ⟨FlatFeed.both_add ha.1 hb.1,(FlatFeed.step_add ha.1 hb.1).trans (by rw [ha.2,hb.2,zero_add])⟩
  | smul k a ha ih =>
    rw [show (k • a) * tests= outside k * (a*tests) from mul_assoc ..]
    constructor
    · rw [mul_left_comm]; apply ih.1.external
    rw [FlatFeed.step_external ih.1, ih.2,mul_zero]

/-- Raw pre-restriction columns `f,g` from stamps etc. Validity at a test mode established also
for any b touched by that test. -/
theorem separatedEquiv [DecidableEq I] (h : (P_ ports).mkQ f=(P_ ports).mkQ g)
    (s : I → Set (Site n)) (hp : ∀ i∈v, LocalOn (s i) (σ i).stencil)
    (he : ∀ i∈v,∀ e∈ports, off e (s i)) (hg : (F).Funded ((W).weight * (f*tests))) :
    (F).Funded ((W).weight * (g*tests)) ∧ (F).step W (g*tests) = (F).step W (f*tests) := by
  obtain ⟨h1,h2⟩:= annihilator hn hv (f:=g-f) ((Submodule.Quotient.eq _).mp h.symm) s hp he -- check
  have hu : g*tests = (g-f)*tests+f*tests:=by ring
  rw [hu, FlatFeed.step_add h1 hg,h2,zero_add]; exact ⟨FlatFeed.both_add h1 hg,rfl⟩

omit hn in
/-- Ghost-free sector closure on any words in the calculation of the Ward contact tests. -/
theorem closedTower :
    let u : BRST.chamber G n := ⟨Stamp.shafts σ v,certified_native hv⟩
    let k : BRST.chamber G n := ⟨coupled a.e a.X u.val, Proxy.couple _ a.valid.acts (certified_native hv)⟩
    let e : BRST.chamber G n := ⟨effort a.e a.X,a.valid.acts.effort _⟩
    let f : BRST.chamber G n := ⟨fallout a.e a.X,a.valid.acts.fallout _⟩
    differential u=0 ∧ differential k=0 ∧ differential e=0 ∧ differential f=0 := by
  intro u k e f; have he : respects u.val:= (Stamp.pre_all ..).gauge
  exact ⟨BRST.invariant u he, BRST.invariant k ((a.valid.contact (certified_native hv) he).gauge),
    BRST.invariant e a.valid.effort.gauge, BRST.invariant f a.valid.fallout.gauge⟩

omit hn hv in
lemma onStamp {d} {C : Family G} (hC : C.Makes) (p : ∀ j, Bid.pop (C.localSection j)) (x : Stamp.Reservation C n d) :
    let f := (Stamp.placed C hC p x).stencil
    let s := (C.localSection x.height).footprint x.anchor
    Proxy f ∧ LocalOn s f := by
  intro f s
  refine ⟨(field_proxy _ (C.localSection x.height) (Pi.single x.leg 1) x.anchor).after (Complex.reCLM) Complex.reCLM.contDiff, ?_⟩
  intro U V h; exact congr_arg Complex.re ((C.localSection _).placed_local x.anchor (Pi.single x.leg 1) U V h)
end YM.FormalOPE.RG10.InversionWard
