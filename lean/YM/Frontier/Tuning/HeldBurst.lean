import YM.Frontier.Tuning.Footage
import YM.Frontier.Tuning.Voice
/-! Concurrent held product income BEFORE normalized score. On the genuine whole-support
flag-free branch, keeps a real catastrophe indicator (never factored as independent warnings).
There is no claim of a complex large-field push law. The shaped estimate tolerates τ-air
markup via half of the poly reserve. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier.Tuning.HeldBurst
open Footage
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Blaze Silica Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Clutch Matter PhysicalNext.Repeat.Alabaster PhysicalNext.Repeat.Height Held ClockShift TwoMotion AngularReceipt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R A : Rep G f} {X : Coat T F} {x :Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {z:E}
variable {H0 a C α Z β γ d η ε σ W s b μ r p q v : ℝ} {j n l : ℕ} {Q : ConnectedActivityE6.Target G P}
variable {o : Target.Order G W}
variable {χ:Chi}
local notation "b₁" => betaF G s L
local notation "M₀" => radiusB s
set_option maxRecDepth 8192
set_option pp.proofs false
set_option maxHeartbeats 1200000

variable {H: Cash W s μ L Q o H0 T R}
variable (P' : Pocket H A j v q C α d γ χ)

def phases (X : Coat T F)(τ:ℂ) (p:Molecule S):=Real.exp ((∑ i∈p.toLeft, ComplexVertex.massPower X i)*Real.log (‖τ‖/τ.re))
def oldword (V:E→ Config G c) (U:E→Directions G f) (u:E→Air f G) (t:E)(I:Config G f)(X:Coat T F)(R:Rep G f)(O:ChartRatio G)(a W:ℝ)(k:Finset ℕ)(Q:ℕ)(τ:ℂ)(e f':Payload G f)(i:Head S):=
  emberC (vary X (V t)) R I (U t) (u t) O a W k τ Q e f' i
abbrev orbitCost (X : Coat T F)(τ:ℂ):Head S→ℝ:= Sum.elim (fun i=>phaseCost τ X i*tag P' 1 (.inl i)) (fun i=>tag P' 1 (.inr i))
lemma prod_cost (p:Molecule S)(τ:ℂ): (∏ i∈p, orbitCost P' X τ i)=phases X τ p * ∏ i∈p, tag P' 1 i:=by
   unfold phases; rw [cumulate p,cumulate p]
   simp only [orbitCost,Sum.elim,Finset.prod_mul_distrib]; rw [mul_assoc]; apply congr_arg (fun x=>x*_)
   rw [← Real.exp_sum, sum_mul]
lemma tokenN (e f':Payload G f)(h: fans R A (grow G L s) e f') {τ:ℂ} (hr:R.beta=τ.re)(hn:‖τ/R.beta‖ ≤ 3) {X : Coat T F} (p:Head S) (hχ : X.χ=χ) (hX:X.x=s)(hM:X.manifest)(hk : X.width=o.K)(hθ:Healthy (Pressure.temp s) (H.supportP p) X.V)
  (V:E→ Config G c)(U:E→ Directions G f)(m:Air f G)(y:E→ Air f G) (t:E) (hf:Mode V t j v)(hs:Clutch X m o.a R.beta q t j V U y):
  let I:=X.input (Vine.worldZ X R.beta m)
  Brush j (orbitCost P' X τ p) (stepspeed P' τ p) (fun z=> oldword V U y z I X R Q.table o.a W k Q.halo τ e f' p) t:=by
 intro I
 rcases p with p|i
 swap
 · change Brush j (rates _ _ ((topStorm S.patch+1)*1) i) _ _ _; rw [mul_one]
   exact P'.impulses τ e f' hr hn h E F X V U y t m hX hk hχ hM hf hs |>.1 i k
 have hc : X.B=M₀ := by rw [Coat.B,hX]
 by_cases he: Packets.connected S Q.halo M₀ p
 swap
 · apply Brush.zi ?_ ?_ (show 0 ≤ stepspeed P' τ (.inl p) by unfold stepspeed; dsimp only [Sum.elim]; unfold phaseSpeed; have hh':= P'.strong; positivity)
   exact Eventually.of_forall fun x=> if_neg (show ¬ Packets.connected S Q.halo X.B p by rwa [hc])
   exact mul_nonneg (Real.exp_nonneg _) (Footage.positive P' zero_le_one _)
 let Gx z:= penGain (vary X (V z)) R I (U z) Q.table τ p
 let gx z:= Polar.stock (vary X (V z)) o.a R W Q.table (U z) I k p
 have Hg(z): oldword V U y z I X R Q.table o.a W k Q.halo τ e f' (.inl p) = Gx z*gx z := if_pos (show Packets.connected S Q.halo X.B p by rwa [hc])
 have hg' : Brush j (tag P' 1 (.inl p)) 1 gx t:=by
   unfold Footage.tag Silica.stout Mixed.costs; dsimp only [Sum.elim]; rw [if_pos he]; exact P'.blanks E F X V U y t m hX hk hχ hM hf hs k p hθ (Packets.shares_nonzero S Q.halo M₀ he)
 by_cases hy :(fun i=> X.enforce o.a (U i) (X.plaza (p.dome (304*X.B))))=ᶠ[𝓝 t] fun _=>0
 · apply Brush.zi ?_ ?_ (show 0 ≤ stepspeed P' τ (.inl p) by unfold stepspeed; dsimp only [Sum.elim]; unfold phaseSpeed; have hh':= P'.strong; positivity)
   · filter_upwards [hy] with i hi; rw [Hg]; rw [show gx i=0 by unfold gx Polar.stock; split; dsimp only; exact mul_eq_zero.mpr (Or.inr hi); rfl]; simp only [Complex.ofReal_zero,mul_zero]
   exact mul_nonneg (Real.exp_nonneg _) (Footage.positive P' zero_le_one _)
 have hz:= P'.impulses τ e f' hr hn h E F X V U y t m hX hk hχ hM hf hs |>.2 p hy
 exact (hz.paints (ComplexBrush.cast hg')).shimmy (Eventually.of_forall Hg)
lemma complete {X:Coat T F}(e f':Payload G f)(h: fans R A (grow G L s) e f') {τ:ℂ} (hr:R.beta=τ.re)(hn:‖τ/R.beta‖ ≤ 3) (p:Molecule S)(hp:troupe T R Q.halo M₀ p) (hχ : X.χ=χ) (hX:X.x=s)(hM:X.manifest)(hk : X.width=o.K)(hθ:Healthy (Pressure.temp s) (H.unionP p) X.V)
  (V:E→ Config G c)(U:E→ Directions G f)(m:Air f G)(y:E→ Air f G) (t:E) (hf:Mode V t j v)(hs:Clutch X m o.a R.beta q t j V U y):
  let K:=X.catastrophe (o.ξ/2) R.beta (blaze p)
  let I:=X.input (Vine.worldZ X R.beta m)
  Brush j (K.indicator (fun _=>phases X τ p*(∏ i∈p, tag P' 1 i)) m) (lumpSum s α d γ j L τ * H.shapeW p)
    (fun z=> ∏ i∈p, oldword V U y z I X R Q.table o.a W k Q.halo τ e f' i) t:=by
   intro Y I
   by_cases he:m∈Y
   · rw [Set.indicator_of_mem he,← prod_cost]; refine (ComplexBrush.allProd p _ _ _ fun i hi=>tokenN _ _ _ h hr hn i hχ hX hM hk (Finset.disjoint_of_subset_left (subset_biUnion_of_mem H.supportP hi) hθ) V U m y t hf hs).climb le_rfl (shellCost _ _ hp _)
   rw [Set.indicator_of_notMem he]; refine Brush.zi ?_ le_rfl ?_
   · dsimp only [Y, catastrophe, Poll.Crash] at he; change ¬(∀ i∈_,∃ j, _≤_ ∧ _≤_) at he; push Not at he
     obtain ⟨i,hi,hb⟩:= he
     have hc : Cash W X.x μ L Q o H0 T R := hX.symm ▸ H
     have hx := hs.sleek hc hf P'.stamp hM hk i (fun i hi=> (hb i hi).le) k
     filter_upwards [hx] with t ht
     exact Finset.prod_eq_zero (i:=Sum.inr (.inr (.inr i))) (mem_toRight.mp (mem_toRight.mp (mem_toRight.mp hi))) ((congr_arg Complex.ofReal ht).trans Complex.ofReal_zero)
   unfold lumpSum; have hv:=P'.strong; have hn:=H.positive_volume p; have hp:=P'.wide; positivity
end YM.Frontier.Tuning.HeldBurst
