import YM.OPE.Compatible.Docks.Swing
/-!
# Earn inverse right with budget. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Yolk
open MeasureTheory Function Filter Set
open Lattice RG Wilson Source Labels Source.Drops
open Pill Asymptotics
open Module Finset
open Drift
open scoped Topology BigOperators Classical ContDiff
variable {I E F J X:Type}{k:ℕ} {f:Filter I}{β p:I→ℝ}{s:ℝ}
section
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F] [NormedAddCommGroup X][NormedSpace ℝ X]
lemma trip (A:I→ E→L[ℝ] X×X)(K:I→F→L[ℝ] X)(X':I→ E→L[ℝ] F×F)(hp:∀ i,A i= doublet (K i)∘L X' i)(Y:I→X→L[ℝ] F)(hx:Wax β f Y 0)(hz:∀ i x,K i (Y i x)=x)(h: ∃ V:I→ (F×F)→L[ℝ] E, Wax β f V 0∧ ∀ᶠ i in f, V i∘L X' i=ContinuousLinearMap.id ..∧ X' i ∘L V i= ContinuousLinearMap.id ..):
       ∃ V:I → (X×X)→L[ℝ] E, Wax β f V 0∧∀ᶠ i in f, A i∘L V i=ContinuousLinearMap.id ..:=by
       simp_rw [hp]; obtain ⟨B,h',H⟩:=h; exact opticsα _ K Y B hx h' (H.mono fun i hi=>hi.2) hz
variable [FiniteDimensional ℝ F]
lemma FindRise (A B:I→ E→L[ℝ] F)(hp:Tendsto β f atTop)(hx:s<0)(hz:Wax β f A 0)(hv:Wax β f (B-A) s)(h: ∃ V:I→ F→L[ℝ] E, Wax β f V 0 ∧∀ᶠ i in f,A i ∘L V i=ContinuousLinearMap.id ..): Wax β f B 0 ∧ ∃ V:I→ F→L[ℝ] E, Wax β f V 0∧∀ᶠ i in f,B i ∘L V i=ContinuousLinearMap.id ..:=by
       refine ⟨(RateLE.add (hv.mono hx.le) hz (carth hp)).congr (Eventually.of_forall (fun i=> sub_add_cancel ..)),?_ ⟩; obtain ⟨V,h,H⟩:=h; exact gritC A B V hp H hx h hv
end
end YM.OPE.Yolk
