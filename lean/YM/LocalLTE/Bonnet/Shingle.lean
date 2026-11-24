import YM.LocalLTE.Bonnet.Lines
/-! Curve control for general retirement.We need through projection labels. Adapted Fend/Asym. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Shingle
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Poll Pond MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Metric Progress.DirectedRecipe Payments Ovens Ovens.Pipes
open Refrain Trio Marlin Slide Push.BetaTransport
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c L C:Side} {B : BudgetPoint} {X Z: Support c} {z w : ℕ} {e p d a δ Y : ℝ} {x:ℝ} {s:Set ℝ} {ι:Type}

namespace Mild

variable {S : StepData c L} {T:Tube G S} {K₀:Teller G} {X : ConnectedActivityE6.Target G K₀} {θ: Target.Order G p} {L₀ : Side}
variable (k ℓ:ℕ) {R: RG.Rep G L} (A: Cash p e d L₀ X θ a T R)
    {D:ℝ→ Offer G c} {V : ℝ→ Collection.Source G c} (he : Compared (Beam.marquee A B) B V s)
    (ht : B.B=radiusB e)
local notation "P₀" => (Beam.marquee A B)
variable (hv:∀ x∈s,∀ i,B.Regular ((Beam.marquee A B).reg i).support ((V x).logRead i))
def omenN (B:BudgetPoint) (A:Cash p e d L₀ X θ a T R) (k ℓ:ℕ) (V:Collection.Source G c) (i:Site c): Config G c→ℝ:= ∑ x∈ Meadow.panelN A ℓ k, Meadow.garnerAt A B i x •(V.logRead x)
include he ht hv
lemma atticN (i:Site c) (hz : ∀ x∈s,D x i= omenN B A k ℓ (V x) i): Mild B (neighbors (Meadow.studioN ℓ X.halo B.B) i) (fun x=>D x i) s:= by
  have hz:∀ x∈s, D x i=∑ x'∈Meadow.panelN A ℓ k, Meadow.garnerAt A B i x' • ((V x).logRead x'):= hz
  let C (x:ℝ) :=∑ x'∈Meadow.panelN A ℓ k, Meadow.garnerAt A B i x' • ((V x).logRead x')
  let t:=neighbors (Meadow.studioN ℓ X.halo (radiusB e)) i
  have ht₀:Mild B t C s:= by
    refine Mild.total (g:=fun x' x=> Meadow.garnerAt A B i x' • (V x).logRead x') (Meadow.panelN A ℓ k) fun p hp=> ?_
    have h:= litIn P₀ p he (fun x hx=>hv x hx p)
    have hl := h.scale (Meadow.garnerAt A B i p)
    by_cases h: Meadow.garnerAt A B i p=0
    · simp only [h,zero_smul]; refine ⟨fun x hx=> CouplingShape.reg_const _,fun x hx i ε he=> ?_⟩; filter_upwards with y; rw [sub_zero]; exact VerifiedReset.sup_le (CouplingShape.sup_const 0) (by rw [abs_zero]; exact he.le)
    exact hl.mono (Meadow.assignedN A B i p hp ht h).2
  have hh:Mild B (neighbors (Meadow.studioN ℓ X.halo (radiusB e)) i) (fun x=> D x i) s:= ht₀.aboard id continuous_id.continuousOn (fun _=>id) hz
  rw [show neighbors (Meadow.studioN ℓ X.halo B.B) i=t from congr_arg (fun y:ℕ=> neighbors (Meadow.studioN ℓ X.halo y) i) ht]; exact hh
end Mild

section inspects
variable {S : StepData c L} {T:Tube G S} {K₀:Teller G} {X : ConnectedActivityE6.Target G K₀} {θ: Target.Order G p} {L₀ : Side}
variable (k ℓ:ℕ) {R: RG.Rep G L} (A: Cash p e d L₀ X θ a T R)
    {D:ℝ→ Offer G c} {V : ℝ→ Collection.Source G c} (he : Compared (Beam.marquee A B) B V s)
    (ht : B.B=radiusB e) {Y:Stars→Side}
    (hv:∀ x∈s,∀ i,B.Regular ((Beam.marquee A B).reg i).support ((V x).logRead i))
    (hx:∀ i,(Y i).val=2*(w+i.val)) {fa:ℝ→∀ i:Stars, Offer G (Y i)} (hf:∀ i j,Mild B univ (fun x=>fa x i j) s)
    (hp:w+4≤ z)
local notation "Z" => (Beam.marquee A B)
include he ht hv hf hp
lemma lightingN (u:Site c) (hw:∀ i∈s,D i u=Mild.omenN B A k ℓ (V i) u) (hs:x∈s): Varies (fun i W=> (∑ j ∈ Meadow.panelN A ℓ k, Meadow.garnerAt A B u j*((Beam.marquee A B).read (V i)|>.regularOccurrence B j W)) - D i u 1 - Trio.unearned B hx z (rip (fa i)) u W) x s:= by
  refine (Varies.sub (Varies.sub ?_ ?_) (glowing hx hf hp u hs))
  · exact Mild.weighted _ fun i h=> variations _ ((litIn Z i he (fun x hx=> hv x hx i)).clipped x hs)
  let p:= Mild.atticN k ℓ A he ht hv u hw; exact p.travels x hs 1 (flat_ok ..)
end inspects
end YM.PhysicalNext.Repeat.Shingle
