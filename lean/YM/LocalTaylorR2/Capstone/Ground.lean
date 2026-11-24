import YM.LocalTaylorR2.Capstone.Lever
/-!
 # All-good in calibration Offers to all-Healthy support on beacons

 Sup bound for error contributions proved without an axial subdomain restriction; actual auth 
 Supports and shared `V` ingredients (Offer dial not resampled independently).
 Adapt Trio.Weld.kinds (only :: stencil rear). -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Capstone
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open PhysicalNext PhysicalNext.Repeat
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard
open Trio
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C' F L:Side} {j i m n W w r k l:ℕ} (B : BudgetPoint) {Y:Stars→Side} {q : ℝ}
section morph
variable {q q' : Stars→ℝ} (Q:∀ i:Stars,(Y i).val=2*(w+i.val)) (z:ℕ) (fa: ∀ i:Stars,Offer G (Y i))
variable (h : ∀ i j, B.Regular univ (fa i j)) (hq : ∀ i,0≤q i) (hp:w+4 ≤ z)
include h hp hq
lemma pace (x:Site c)
    (hf:∀ (i:Stars) (U:Config G (Y i)), flags B.threshold U=∅ → ∀ l:List (Directions G (Y i)), l.length≤B.order → (∀ v∈l, ‖v‖ ≤ B.threshold) → ‖leftDerivs (Boulevard.stillA (Trio.froth (fa i))) l U‖ ≤ q i) :
    B.Regular (neighbors z x) (Trio.ornament Q fa x) ∧
    B.supBounds x (neighbors z x) (Trio.ornament Q fa x) (oroW B z q):= by
  rw [orchard]; let p i:= Boulevard.stillA (Trio.froth (fa i))
  have hh i:B.Regular univ (p i):= by
    have hx : B.Regular univ (froth (fa i)):= by rw [show froth (fa i)=∑ j,fa i j from funext fun i=> (Finset.sum_apply ..).symm]; exact Meadow.regularA _ fun j _=> h i j
    exact CouplingShape.reg_sub hx (CouplingShape.reg_const _)
  have hz i (j:Site (Y i)): separation x (Slide.sites (pad Q i) x j)≤z:= (Slide.village (C:=Y i) (w:=w+i.val) (Q i).ge _ _).trans (by have hk := i.isLt; omega)
  have h' i: B.Regular (neighbors z x) (Slide.ray i • (p i∘ Slide.shape (pad Q i) x)) := CouplingShape.reg_scale _ (Slide.regular (pad Q i) x (hh i) fun j=> (neighbors_mem ..).2 (hz i j))
  refine ⟨Meadow.regularA _ (fun i _=> h' i),?_⟩; apply Trio.sup_S (B:=B) _ _ _ _ _ (fun i _=> h' i)
  intro i _; apply CouplingShape.sup_scale _
  refine ⟨mul_nonneg (by unfold Trio.tilt; positivity) (hq i),fun V hu l hl hd=>?_⟩
  let W:=Slide.shape (pad Q i) x V; have hK := Trio.hint Q z V i hp x hu
  apply Slide.stalled (pad Q i) x (p i) (hz i) l V hl hd ((hh i).smooth _ (by unfold Healthy; rw [hK]; simp))
  exact hf i W hK

-- linear in Offers (even outside all masks); important since subtracting true Omega budgets below
omit h hp hq
lemma offers_add (x:Site c) (fc fd:∀ i,Offer G (Y i)) (he:fa=fc+fd):
    Trio.ornament Q fa x=Trio.ornament Q fc x+Trio.ornament Q fd x:= by
  rw [he,Trio.orchard,Trio.orchard,Trio.orchard,← sum_add_distrib]
  apply sum_congr rfl; intro i _
  have h:∀ v,Trio.froth ((fc+fd) i) v=Trio.froth (fc i) v+Trio.froth (fd i) v:= fun _=> by simp_rw [Trio.froth,Pi.add_apply,sum_add_distrib]
  ext1 v; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Function.comp_apply,Boulevard.stillA] at *; rw [h,h]; ring
end morph
end YM.LocalTaylorR2.Capstone
