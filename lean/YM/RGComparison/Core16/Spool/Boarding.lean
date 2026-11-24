import YM.RGComparison.Core16.Spool.Transfer
import YM.RGComparison.Core16.Leading
/-! # Adaptor for the specialization also through the fixed-volume path formula checkpoint1

If testing THAT path through same actual one-step posterior, pay that estimator's
`w` (previous theory) on same fields for re-expression. Doesn't require calling CP1 bills to call CP5.
Post-summation orientations, no declaring equality of fuel on different support labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Spool
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Forge
open PertExtension PertExtension.Series Tested Radial Therm Precision
open Lumen Lumen.Planet Parcel Parcel.Oven Next.Fluctuations Finset Complex Analysis
open Lumen.Stage
open scoped Topology ContDiff BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge} {κ:ℝ} {ι:Type}[Fintype ι] {c f : Side} (J:ι→Lamp G) (S:StepData c f) (T:Forest S.ratio)
    {P: Oven S.patch}(X:P.Form G)(Z:ChartRatio G)(p:ι→ Site f)
local notation "d" => Descent.push S T Descent.nil

lemma plain (hp:P.Offers X S.kernel)(hs:Bid.Larger (G:=G) S)(he:LocalRatio Z) :
   Descent.Testable d (column J p) → Descent.grade d (column J p) (power J) → Spool.rank J S T X Z 0 p=WilsonXLocal.kernel Z d 0 (column J p) (power J):=by
   intro h hG
   have hd: Descent.Room (G:=G) d:= ⟨hs,trivial⟩
   have hx : ∀ i:Edge _,‖(0:Directions G c) i‖ ≤ X.Q:=by simp [hp.good.thick.1.le]
   let A (b) := Descent.ranking Z d 0 (look b ∘ column J p)
   let w:=power J; let f g:=reads J S 0 p g
   have hb (b:Bool) (g:ℝ) : look b (f g) = g⁻¹^w • Descent.conditioned d (Descent.offset 0 g) (look b ∘ column J p) 1:=by
      have hq: slice (0: Directions G c) g=1:=by funext i; simp [slice]; try rfl
      unfold f; rw [descended J S (0:Directions G c) p g T (β:=Descent.offset 0 g) (by simp [Descent.offset]),map_smul,hq,WilsonXLocal.measured (look b) _ (Descent.room_ok _ hd) h.neat]
   have h (b:Bool): Aspiration (look b ∘ f) (fun j=> A b (w+j)):=by
      rw [show look b ∘ f= _ from funext (hb b)]; exact Descent.rescaled_formula Z he hd 0 (WilsonXLocal.tested (look b) h) (WilsonXLocal.wanted (look b) hG)
   funext j; apply Complex.ext
   · exact congr_fun ((forecast J p false hp hs hx T he).unique (h false)) j
   exact congr_fun ((forecast J p true hp hs hx T he).unique (h true)) j
end YM.RGComparison.Core16.Spool

