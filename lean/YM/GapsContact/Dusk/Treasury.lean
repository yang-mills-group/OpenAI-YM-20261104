import YM.TraceExtension.Terrace.Base
import YM.GapsContact.Dusk.Shift
/-! Fiat charge issue: must be polynomial of reference power after EXP. -/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Dusk
open Function Filter Set Lattice RG RG.Supply Wilson Push.PriceCompiler Push.GridApprox Vac
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}

def customs (G:Gauge):=2*Module.finrank ℝ G.Mat+ (1:ℝ)
def Feasible (A:Levels G): Prop:= ∀ i,fiat G (A.params i) (A.clock.hatBeta i) ≤ customs G*gate (A.clock.hatBeta i)
lemma reserve {X:Sheet G} {D:Rolls X} {T:Protection D} (V:Delays T) : ∃ W,DelayLe V W∧∀ Y,DelayLe W Y→∀ (Z:Bar Y)(I:Wait Z)(A:Levels G), Paid I A→ Feasible A:=by
    let P(i:ℕ)(x:ℝ): Prop := fiat G (X.profile i) x ≤ customs G*Real.log x
    have he(i:ℕ):∀ᶠ x in atTop,P i x:=by
       let f:= fiat G (X.profile i) 1; have ht(x:ℝ): fiat G (X.profile i) x=f+2*Module.finrank ℝ G.Mat* Real.log x:=by unfold f fiat; rw [Real.log_one]; ring
       filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop f] with x hx; unfold P; rw [ht]; unfold customs; linarith
    obtain ⟨y,-,hy,ht⟩:= collect_upper V.betaEntry _ (fun j=> eventually_transitions j atTop _ (fun i _=> he i))
    refine ⟨{V with betaEntry:=y},⟨hy,le_rfl,le_rfl,le_rfl⟩,fun W hw Z I A h m=>?_⟩; rw[params_eq h]; exact ht (A.clock.J (m+1)) _ ((hw.beta _).trans (h.pays m)) _ (step_paid _ _)
end YM.GapsContact.Dusk
