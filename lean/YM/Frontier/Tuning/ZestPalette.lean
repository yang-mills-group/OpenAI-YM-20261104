import YM.Frontier.Tuning.GlassLog
import YM.Frontier.Tuning.Held
import YM.Frontier.Tuning.TwoMotion
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Fairum

/-! Uniform Zest for entries with pruned parameters. Variables can be held arbitrary near original coarse configuration. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Frontier.Tuning.ZestPalette
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Blaze PhysicalNext.Repeat.Alabaster
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Eider Flux Held GlassLog Zest TwoMotion
open Blaze PhysicalNext.Repeat.Alabaster
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {E A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x:E}
variable {j n : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {X : Coat T F} {a W : ℝ} {C : E → Config G c}
variable (H : Glass P X C x j W) {Y : A→ F.Slice G} (U : A→ Config G f) {Ñ : ChartRatio G} {R R': Rep G f}
variable {u : A→ E → Directions G f} {w : A→ E → Air f G} {k : Finset ℕ} (hq : Room P S T X.x)

def Bound (t:A→ℂ) (x:E) (k:ℕ) := Zest (fun i (_:E)=>t i) x k
lemma constant {g:A→ℂ}{b:ℝ}(hb:0≤b)(hg:∀ u, ‖g u‖≤b) : Bound g x j := Zest.parallel hb hg
lemma zmul {f g:A→E→ℂ} (h:Zest f x j)(p:Zest g x j) : Zest (fun i y=>f i y*g i y) x j:= (h.pair p).wand (p:=fun z=>z.1*z.2) (by fun_prop)
lemma zcast {f:A→E→ℝ}(h:Zest f x j) : Zest (fun i y=>(f i y:ℂ)) x j:= h.replay (Complex.ofRealCLM)
lemma zexp {f:A→E→ℂ} (h:Zest f x j): Zest (fun i y=>Complex.exp (f i y)) x j:=h.wand ((show ContDiff ℂ (j:WithTop ℕ∞) Complex.exp from Complex.contDiff_exp).restrict_scalars ℝ)
lemma fullC {ι:Type} (s:Finset ι) (f:ι→ A→E→ℂ) (hv:∀ i∈s,Zest (f i) x j) : Zest (fun i y=> ∏ z∈s,f z i y) x j:= by
  induction s using Finset.induction_on with
  | empty=> simpa only [Finset.prod_empty] using Zest.still (x:=x) (A:=A) (k:=j) (1:ℂ)
  | insert i s hi hh=> simp_rw [Finset.prod_insert hi]; exact zmul (hv i (Finset.mem_insert_self ..)) (hh fun j hj=> hv _ (mem_insert_of_mem hj))

set_option linter.unusedFintypeInType false
include H hq
lemma held (hU : Zest u x j) (hw: Zest w x j)(he : Intake P T X.x R) (he' : Intake P T X.x R') (hv: Facing R R')
    (Ñ:ChartRatio G) (k : Finset ℕ) (l : ℕ) (a : ℝ) (ha : 0<a*X.t) (ht : 4*a*X.t < Ñ.radius) (hΛ : LocalRatio Ñ)
    (τ r s p q: A→ℂ) (hr:Bound r x j)(hs:Bound s x j)(hp:Bound p x j)(hq':Bound q x j)
    (hτ:Bound τ x j)(hlog:Bound (ComplexVertex.logMass Ñ ∘ τ) x j) (i:Head S):
  Zest (fun t y=> emberC (drive X (C y) (Y t)) R (U t) (u t y) (w t y) Ñ a W k (τ t) l (traitE R R' (r t) (s t)) (traitK R R' (p t) (q t)) i) x j:=by
  let X' y t:=drive X (C y) (Y t)
  have hh:=H.glassy (Y:=Y) U hq u hU he k l ha ht hΛ i hw
  have hh':=H.glassy (Y:=Y) U hq u hU he' k l ha ht hΛ i hw
  rcases i with i|i|i|i
  · change Zest (fun t y=> if connected S l X.B i then (_:ℂ) * (stock (X' y t) a R W Ñ (u t y) (U t) k i:ℝ) else (0:ℂ)) x j
    split_ifs with he''
    · replace hh : Zest (fun t y=> stock (X' y t) a R W Ñ (u t y) (U t) k i) x j := hh.congr (Eventually.of_forall (fun y t=> if_pos he''))
      replace hh:= zcast hh
      refine zmul (zexp ?_) hh
      have hg:=penZest H (Y:=Y) U hq i hU
      change Zest (fun t y=> (τ t-Complex.ofReal R.beta) * ↑(-(chalky (X' y t) (u t y) (U t) i+crispy (X' y t) i):ℝ) + ((X.pens i).card:ℂ) * (ComplexVertex.logMass Ñ R.beta-ComplexVertex.logMass Ñ (τ t))) x j
      exact (zmul (Zest.plusminus hτ (Zest.still _)) (zcast hg.against)).together (zmul (Zest.still _) ((Zest.still _).plusminus hlog)) -- hτ not Zest reducible notation?
    exact Zest.still _
  · change Zest (fun t y=>sheath (X' y t) a R _ _ i) x j at hh
    change Zest (fun t y=>sheath (X' y t) a R' _ _ i) x j at hh'
    exact ((zmul hp (zcast hh)).together (zmul hq' (zcast hh'))).congr (Eventually.of_forall fun y t=>(mix_K (f':=traitK R R' (p t) (q t)) (X' y t) R (U t) (u t y) (w t y) Ñ a W k (τ t) R' (fun _ _=>rfl) hv i l).symm)
  · apply Zest.plusminus (zexp (show Zest (fun t y=> comboLog _ _ _ _ _ _ _ _ _ i) x j from ?_)) (Zest.still _)
    have hL:=logZest H (Y:=Y) U hq u hU he ha ht hΛ i hw
    have hL':=logZest H (Y:=Y) U hq u hU he' ha ht hΛ i hw
    rcases i with (i|i)|i
    · exact ((zmul hr (zcast hL)).together (zmul hs (zcast hL'))).congr (Eventually.of_forall fun y t=>(mix_log (e:=traitE R R' (r t) (s t)) (X' y t) R (U t) (u t y) (w t y) Ñ a (τ t) R' (fun _ _=>rfl) hv i).symm)
    all_goals change Zest (fun t y=> (if flips _ _ _ then τ t/(R.beta:ℂ) else 1) * Complex.ofReal _) x j
    all_goals simp_rw [div_eq_mul_inv]; split_ifs
    all_goals first | exact zmul (zmul hτ (Zest.still _)) (zcast hL) | exact zmul (Zest.still _) (zcast hL)
  change Zest (fun t y=>Polar.sprinkle (X' y t) a R W _ _ k i) x j at hh
  exact zcast hh

lemma heldFlo (hU : Zest u x j) (hw: Zest w x j)(he : Intake P T X.x R) (he' : Intake P T X.x R') (hf: Facing R R') (l:ℕ) (ha : 0<a*X.t)
    (ht : 4*a*X.t < Ñ.radius) (hΛ : LocalRatio Ñ) {τ:A→ℂ}{vM bM:ℝ}(hM:∀ t, ‖τ t‖ ≤ vM ∧ ‖ComplexVertex.logMass Ñ (τ t)‖ ≤ vM)
    {e f':A→Payload G f}(hv : ∀ i, fans R R' bM (e i) (f' i))(i:Molecule S):
    Zest (fun t y=>∏ z∈i, emberC (drive X (C y) (Y t)) R (U t) (u t y) (w t y) Ñ a W k (τ t) l (e t) (f' t) z) x j:=by
    choose r s p q h1 h2 h3 h4 hx hy using hv
    simp_rw [hx,hy]
    apply fullC
    intro i hi
    by_cases h:Nonempty A
    · have hg : 0≤ bM := (norm_nonneg _).trans (h1 h.some)
      have hg' : 0≤ vM := (norm_nonneg _).trans (hM h.some).1
      exact held H U hq hU hw he he' hf Ñ k l a ha ht hΛ τ r s p q (constant hg h1) (constant hg h2) (constant (by positivity) h3) (constant (by positivity) h4)
        (constant hg' fun i=>(hM i).1) (constant hg' fun i=>(hM i).2) i
    exact ⟨0,le_rfl,Eventually.of_forall fun i a=>(h ⟨a⟩).elim⟩
end YM.Frontier.Tuning.ZestPalette
