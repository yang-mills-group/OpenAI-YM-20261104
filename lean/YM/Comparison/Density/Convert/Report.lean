import YM.Comparison.Density.Convert.Joining

/-!
# Short-packet comparison on the full representation

This is a consumer; premise `Gain` has NO bound
on the closure's rendered group EBound. It describes the RG1/02
PRE-conversion comparison to the rendered formal model. Includes
appropriate signed old masks. Canonical base mismatch must be in
one of the packets or retained as a separately rendered/calibration
term. This theorem does no projection of the scalar or kinetic data;
their consumers must require an actual `Resolution` (later).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Convert
open Fusing Transport RG Lattice Wilson Markers Registers Testing MeasureTheory
open Function Finset Push.AbsoluteSums Marker Multi
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side}
variable {V : Type} [DecidableEq V] {R : Census V} {X : V → Type} [∀ v, NormedAddCommGroup (X v)] [∀ v, NormedSpace ℂ (X v)]

section Loosen
variable {B : BudgetPoint} {e s : ℝ} {P : Activities G n}
lemma plain (h : 0≤e) (H : P.EBound (later B e h) s) : P.EBound B s := by
  obtain ⟨b,hb,hr⟩:= H
  refine ⟨b,hb,fun x=>budget_mono (hr x) (fun j=>?_) (fun j=>?_)⟩
  · split; exact mul_nonneg (Real.exp_pos _).le (hb _).1; exact le_rfl
  split_ifs
  · refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ (by positivity))) (hb j).1
    exact le_add_of_nonneg_right h
  exact le_rfl
end Loosen

variable [Fintype V]

/-! `Gain` retains one representation of the model (Z contains its
specified path array and analytic packets/admitted masks) and one rough
error representation. Each input rough term here already has its
own full support and interpretation. Likewise the subtracted analytic
rendering on Z. All letters T/Short have real origins and carry the
actual signs/markers ADDRESS-BY-ADDRESS. Analytic higher-output
regular extension lives on closed-healthy. Log identities in Gain
must be on the actual masks (may be established without using jets,
only by splitting exact analytic series and retaining actual masks).
In particular setting all flags failed output to zero by default would
not supply this premise unless proved to implement these equalities
at every indicated field.

`bE` includes the C_J/L estimate on incoming rough in RG1; can also
track e^natural separately by applying `weave`. `a...` units are
local logs, force units BEFORE division. No factor paid by regular
length alone supplies `b` in Gate. `D` is regular rendered answer,
NOT an assertion of its formal coefficient correctness. -/
structure Gain (P Z : Rep G n) (Q : Assembly R X G n)
    (D F : Registers R X G n) (A : Activities G n) (T : Menu R X G n) (L : Start G n) : Prop where
  side : P.p=Z.p
  vacuum U : P.exponent U = Z.exponent U-A.additive P.p U - ∑' i,∑ x,(L i).comes x U
  sources x U : Q.exponent.log P.p x U = D.log P.p x U+F.log P.p x U+ journal T x U

/-- Physical premises on the pre-merger. -/
structure Gate (P Z : Rep G n) (Q : Assembly R X G n)
    (D F : Registers R X G n) (A : Activities G n) (T : Menu R X G n) (L : Start G n)
    (K : LinkTube G) (O : Readers V X n) (w : V→ℝ)
    (v c b δF δR aE uE aG bE bG pZ pY pX r g q m : ℝ) : Prop where
  -- reserves δF or δR on the Output. One extra exponent spent on merger
  ample : 0≤δF
  reserve : 0 ≤ δR
  tender i : 0<w i
  ticks : Assembly.Tidy P w O Q v c (δF+1) b
  regularZ : Art Z.activities Z.p
  roughE : Art A P.p
  moves s b : Nonempty (P.activities.Moves s b)
  force : P.activities.ForcedFamily P.p
  permits s b : Nonempty (Z.activities.Moves s b)
  rough s b : Nonempty (A.Moves s b)
  boundZ : Z.activities.EBound (later P.p δR reserve) pZ
  givenGraph : D.Layout P.p O
  givenPrice : D.Budget (later P.p δR reserve) O w pY pX
  roughPrice : A.EBound (later P.p δR reserve) aE
  unstructured : Layout P.p O F
  tagRough : F.Budget (later P.p δR reserve) O w r g
  sails : Cleared P.p K L bE aG (δF+1) δR
  detail : Hatch P.p K O T bG uE (δF+1) δR w
  out : 1≤q
  gate : 0 ≤ m
  seed : ((P.p.B+P.p.B+1:ℕ):ℝ)^4*m ≤ 1
  bought : q*b + (aG+uE)*Real.exp (aG+uE) ≤ m

section Report
variable {P Z : Rep G n} {Q : Assembly R X G n} {D F : Registers R X G n} {A : Activities G n} {K : LinkTube G}
variable {T : Menu R X G n} {L : Start G n}
variable {O : Readers V X n} {w : V→ℝ}
variable {v c b δF δR aE uE aG bE bG pZ pY pX r g q m κ : ℝ}

/-- Literal error REGULAR families. Spare K of A unchanged here; only
attach's K will occur in the eval. Contrast doing a pointwise infimum over
sources. -/
def uncertain (L : Start G n) (A : Activities G n) : Activities G n:= weave A (earnings L A)
def inserted (T : Menu R X G n) (O : Readers V X n) (F : Registers R X G n) := alongside F (bonded O T)
def destination (Z : Rep G n) (A : Activities G n) (L : Start G n) :=
    {Z with activities:= weave Z.activities (uncertain L A)}
def destinationM (D F : Registers R X G n) (T : Menu R X G n) (O : Readers V X n) :=
    alongside D (inserted T O F)

def outcome (P Z : Rep G n) (A : Activities G n) (L : Start G n) (O : Readers V X n) (T : Menu R X G n): Rep G n:=
    Fusing.boundAlong P (destination Z A L) (Convert.change P.p O L T)
def output (P : Rep G n) (Q : Assembly R X G n) (D F : Registers R X G n) (L : Start G n)
    (O : Readers V X n) (T : Menu R X G n): Assembly R X G n := Fusing.restored P Q (destinationM D F T O) (Convert.change P.p O L T)

variable (h : Gate P Z Q D F A T L K O w v c b δF δR aE uE aG bE bG pZ pY pX r g q m) (he : Gain P Z Q D F A T L)

include h
omit [Fintype V] in
lemma realError : Fusing.Art (uncertain L A) P.p ∧ (uncertain L A).EBound (later P.p δR h.reserve) (aE+bE) :=
    ⟨weave_art h.roughE h.sails.smoothE, weave_bound h.roughPrice h.sails.meetsE⟩
lemma markError : Layout P.p O (inserted T O F) ∧ Budget (later P.p δR h.reserve) O (inserted T O F) w r (g+bG) := by
  exact ⟨alongside_layout h.unstructured h.detail.shell,by simpa only [add_zero,inserted] using alongside_budget h.tagRough h.detail.costs⟩
lemma markOut : Layout P.p O (destinationM D F T O) ∧ Budget (later P.p δR h.reserve) O (destinationM D F T O) w (pY+r) (pX+(g+bG)) :=
    ⟨alongside_layout h.givenGraph (markError h).1,alongside_budget h.givenPrice (markError h).2⟩
include he
lemma road : Conversion P Q (destination Z A L) (destinationM D F T O) (Convert.change P.p O L T) := by
  have hab:=plain h.reserve h.roughPrice
  have hae:=plain h.reserve (realError h).2
  have hp: (earnings L A).EBound P.p bE := plain h.reserve h.sails.meetsE
  constructor
  · exact he.side
  · intro U
    rw [he.vacuum, counted h.sails]; unfold destination Rep.exponent; dsimp only
    rw [←he.side,weave_summed (plain h.reserve h.boundZ) hae,uncertain, weave_summed hab hp]
    linarith [(h.sails.given_paid (R:=A) U).2]
  intro x U
  obtain ⟨hd,hE⟩:= markError h
  rw [he.sources, entry_bill h.tender h.detail (L:=L),destinationM,alongside_log (Budget_smaller h.reserve h.tender _ h.givenPrice)
    (Budget_smaller h.reserve h.tender _ hE) h.givenGraph hd h.tender x U,
    inserted,alongside_log (Budget_smaller h.reserve h.tender _ h.tagRough)
      (Budget_smaller h.reserve h.tender _ h.detail.costs) h.unstructured h.detail.shell h.tender x U]; abel

lemma inserted_budgets : Assembly.Tidy (outcome P Z A L O T) w O (output P Q D F L O T) (pY+r) (pX+(g+bG)) δF ((Real.exp m-1)/q) :=
    Fusing.extent h.tender h.ample h.ticks (admissible_change h.sails h.detail) (costs_change h.tender h.sails h.detail) h.out h.gate h.seed h.bought h.force (he.side.symm) (markOut h).1 (Budget_smaller h.reserve h.tender _ (markOut h).2)

lemma enacted (x : Cross X) : (output P Q D F L O T).eval (outcome P Z A L O T) x = Q.eval P x:=
    funext fun U=> Fusing.enact h.tender h.ample h.ticks (admissible_change h.sails h.detail) (costs_change h.tender h.sails h.detail) x U (road h he)
lemma vac_too : (outcome P Z A L O T).eval = P.eval := by
  have hQ:= inserted_budgets h he; funext V; apply Complex.ofReal_injective
  rw [← Assembly.zero_order h.tender h.ample hQ 0, enacted h he,Assembly.zero_order h.tender (h.ample.trans (le_add_of_nonneg_right zero_le_one)) h.ticks]

lemma forced_too (hq : 0 < κ) :
    let Y:= outcome P Z A L O T
    Y.activities.ForcedFamily Y.p ∧ Y.activities.KBound (later P.p δF h.ample) ((Real.exp m-1)/q) ∧
      (∀ s b, Nonempty (Y.activities.Moves s b)) ∧ Account (later P.p δF h.ample) w O.source (ranges Y.activities) (output P Q D F L O T).arms κ (((Real.exp m-1)/q)/κ) := by
  intro Y
  have hm s b : Nonempty ((destination Z A L).activities.Moves s b) :=
    ⟨weave_moves ((h.permits s b).some) (weave_moves ((h.rough s b).some) (h.sails.moved ((h.rough s b).some)))⟩
  exact progress (Z:=destination Z A L) h.tender h.ample h.ticks (admissible_change h.sails h.detail) (costs_change h.tender h.sails h.detail) h.out h.gate h.seed h.bought h.force he.side.symm (markOut h).1 (Budget_smaller h.reserve h.tender _ (markOut h).2) h.moves hm hq

/-- Main conditional consumer, BEFORE affine and canonical
readjustments. Requires rough term & rendered answer from Step, incl
separate budgets. Shows where *each* of the prices is evaluated. -/
theorem transport_all (hq : 0 < κ) :
    let Y := outcome P Z A L O T
    let M := output P Q D F L O T
    let E := uncertain L A
    let S := inserted T O F
    let B:= later P.p δR h.reserve
    let B' := later P.p δF h.ample
    Y.path=Z.path ∧ Y.clip=Z.clip ∧ Y.beta=Z.beta ∧ Y.v=Z.v ∧ Y.p=P.p ∧
    (∀ x, M.eval Y x=Q.eval P x) ∧ Y.eval=P.eval ∧
    M.Tidy Y w O (pY+r) (pX+(g+bG)) δF ((Real.exp m-1)/q) ∧
    Y.activities.reg=(weave Z.activities E).reg ∧ Y.activities.E=(weave Z.activities E).E ∧
    Art E P.p ∧ E.EBound B (aE+bE) ∧ Art Y.activities P.p ∧ Y.activities.EBound B (pZ+(aE+bE)) ∧
    M.exponent=alongside D S ∧ S.Layout P.p O ∧ S.Budget B O w r (g+bG) ∧
    M.exponent.Budget B O w (pY+r) (pX+(g+bG)) ∧
    Y.activities.ForcedFamily Y.p ∧ Y.activities.KBound B' ((Real.exp m-1)/q) ∧
    (∀ s b,Nonempty (Y.activities.Moves s b)) ∧ Account B' w O.source (ranges Y.activities) M.arms κ (((Real.exp m-1)/q)/κ) := by
  obtain ⟨h₁,h₂⟩:= realError h; obtain ⟨h₃,h₄⟩:= markError h
  exact ⟨rfl,rfl,rfl,rfl,he.side.symm,enacted h he,vac_too h he, inserted_budgets h he,rfl,rfl,h₁,h₂,
     weave_art (he.side.symm ▸ h.regularZ) h₁, weave_bound h.boundZ h₂,rfl,h₃,h₄,(markOut h).2,forced_too h he hq⟩
end Report
end YM.Comparison.Density.Convert
