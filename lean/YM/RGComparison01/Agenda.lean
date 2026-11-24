import YM.UVExtension.Gale.Swap

/-!
# Financing strengthened estimates at the actual comparison witness

A fairly general hook into the common physical construction. Strengthened
analytic estimates will typically cost:

* a *pre-block* gate (e.g. weighted support and inherited-qev choices);
* selections once block ratios have anticipated those costs;
* *post-block* constants (e.g. high-analytic order bounds);
* tests paid by the scale **delays** depending on those constants.

Hook between `Repeat.Roost.uv_commerce` and
`Repeat.Legato.uv_wishes`. Both TARGET price and RECORD data of the
real Factor available. In particular after asking for extra delays, we will
use the SAME calendar, cost data, shot prescription, labels, common UV and
phase witnesses; not pay existing conclusions at one set then demand price
comparisons at another.

As usual requests are quite explicitly conditional till an instance is
bought. In `Agenda` the factors can use only the prices and delays actually
chosen, not the particular Level comparator. This hook doesn't cover all
potential multi-scale programme rescheduling. Use `Payable.and` for
combining with additional physical obligations.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open Push.PriceCompiler Further.StrongStartup SectorNext
open PhysicalNext PhysicalNext.Repeat
open ThroughLaunch Roof
open Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge}

/-- Demand on the annotated prices/gates, not on the unshot Families. -/
def Agenda (G : Gauge) := (X : Metals G) → (D : Rolls X.p) → (R : Targets X.p X.K) → (E : Expenses R) → Programs X.p → Return.Wages → Return.Wages → (ℕ → ℕ → ℕ) →
    (u : ℕ→ℝ) → (w : Return.Wages) → PhysicalNext.Repeat.Register D E w u →
    (F : ℕ → ℕ → Postage) → Time.Scouts (F:=F) → PostCost D →
    (ℕ → ℕ → JointLoad.Heir.Record) → (ℕ → ℕ → JointLoad.Clockwork.Menu) → (θ : Protection D) → Delays θ → Prop

namespace Agenda
variable (K' : Agenda G) {M : Metals G} {D : Rolls M.p} {A : Alloy M D}

def atFactor (R : Factor A) : Prop := K' M D R.target R.expense R.prices R.v R.t R.span
  R.duration R.walls R.shape R.book R.scout A.post R.recordP R.menu A.θ A.delay

/-- A quantitative analytic bill at these pre-L choices AFTER actual
allocation of certain pre-pledged RECORD data. `p.ε` condition used by the
vacuum inherited-E tests. Widen if another consumer needs earlier say.
Notice inclusion of arbitrary ratio l:ℕ→ℕ. -/
def Invests (s : Sheet G) (T : MapPrices) (R:Targets s (UVExtension.Case.actualPay s T))
    (E : Expenses R) (C : Programs s) (z : Return.Wages) (k : ℕ→ℕ) :=
  ∀ L : ℕ → ℕ, k ≤ L → ∀ D : Rolls (ThroughLaunch.raise s L),
    ∀ (u : ℕ→ℝ) (w : Return.Wages) (R' : PhysicalNext.Repeat.Register D E w u)
      (F : ℕ → ℕ → Postage) (S : Time.Scouts (F:=F)) (P : PostCost D)
      (p : ℕ → ℕ → JointLoad.Heir.Record) (Q : ℕ → ℕ → JointLoad.Clockwork.Menu),
    (∀ j i,StepStages j i → s.first ≤ i → (p j i).ε ≤ 1/4) → ∀ (θ : Protection D) (V : Delays θ),
      ∃ X : Delays θ, DelayLe V X ∧ ∀ Y : Delays θ, DelayLe X Y →
        K' (UVExtension.Case.provider s T L) D R E C z (rays s) mile u w R' F S P p Q θ Y

/-- Produced only after proving the demanded costs. -/
def Payable := ∀ (s : Sheet G) (T : MapPrices) (V : Programs s) (z : Return.Wages) (R : Targets s (UVExtension.Case.actualPay s T))
    (E : Expenses R),
    (∀ i k,(R i k).table=chart G ∧ (R i k).halo=500 ∧ (E i k).earn=Roof.rays s i k ∧
      (E i k).wanting=-(7/16:ℝ) ∧ (E i k).degrees=0) → ∃ k, Invests K' s T R E V z k

def both (L : Agenda G) : Agenda G := fun X D R E C z t n u w T F S P p Q θ V =>
  K' X D R E C z t n u w T F S P p Q θ V ∧ L X D R E C z t n u w T F S P p Q θ V

variable {K'}
theorem Payable.and {L : Agenda G} (h : Payable K') (g : Payable L) : Payable (both K' L) := by
  intro s T u z R E hx
  obtain ⟨k,hk⟩ := h s T u z R E hx
  obtain ⟨l,hL⟩ := g s T u z R E hx
  refine ⟨k ⊔ l,fun L he D u' w R' F S P p Q hp θ V=>?_⟩
  obtain ⟨X,hV,hX⟩ := hk _ (le_sup_left.trans he) D u' w R' F S P p Q hp θ V
  obtain ⟨Z,hφ,hZ⟩ := hL _ (le_sup_right.trans he) D u' w R' F S P p Q hp θ X
  refine ⟨Z,hV.trans hφ,fun _ he=> ⟨hX _ (hφ.trans he),hZ _ he⟩⟩

theorem both_atFactor (K L : Agenda G) (R : Factor A) : (K.both L).atFactor R ↔ K.atFactor R ∧ L.atFactor R := Iff.rfl
end Agenda
end YM.RGComparison01
