import YM.QuadraticLocal.Kiosk
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
section marlin
open PhysicalNext PhysicalNext.Repeat AnalyticBridge.VerifiedReset Marlin Collection Animals
variable (P' : Listing G n)(z s:ℕ)(A: Collection.Source G n) (k t: Trio.Offer G n)
variable (h:∀ i, Trio.Tidy p (neighbors s i) (t i))(ht:∀ i U,t i U≠0→¬Healthy p.threshold (neighbors s i) U)
local notation "d"=> bison A k t
local notation "L"=> lodge P' z s
local notation "q"=> (p.supportExponent+1)
variable (hv:∀ i V, ‖t i V‖≤ a)(he:∀ i:Site n,(coverNumber p.B (neighbors s i):ℝ) ≤ b)
include h ht hv he
lemma launchTrace (hR:Rates p.B f e (tithe s a p b) y): ∃ K : First p (P'.read A) ((pluck p L).read (poursP p L d)) e f q, K.tap.logarithm=(bison A k t).logarithm := by
   have ha:0≤a:= (norm_nonneg _).trans (hv 0 1); obtain ⟨hq,hG⟩:= Marlin.caps P' z s p a ha he
   exact ⟨⟨L,d,hak _,rfl,rfl,rfl,rfl,_,_,sheath P' z s A k t h ht,⟨ _,hq,Marlin.softly A t a hv k,hG⟩,hR⟩,rfl⟩
end marlin
end YM.QuadraticLocal.Kiosk
