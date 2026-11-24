import YM.MatchingLedger.Compass.Hills

/-!
# Trajectory of Wilson PT logarithmic 2, witnesses

Implicit **independent** coefficient program: defined using critical phase evaluation
 & nondegenerate Hessian with the full exponential Haar germ in ANY torus tilt of the
 prescribed StepData (including determinant). Field-insertion free at this point. The
 label/address/model class here is `PathData`. Uses physically natural solution space
 accounting for symmetries, decay and zero kinetic jets; nonunique path representations
 may be used for *solving*; predictions consumed are synthesized tensors uniquely
 determined by these equations. NOT fitting any entries to `C.rep`. Gamma, Theta here
 need only be pointwise in m and in this program only set R requirements.

 Classical run: on each step stationary-phase tree Hessian and
 CRIT value determine next mainTerm jet through field rank 4. G loop:
 input's carry up to rank 2 is fully used before extracting pure thermal determinant,
 normalize residual Hessian in PERIOD LIMIT to the matched one-loop curvature of our chosen
 principal with one scalar `α` allocated to common adjacent coupling; use `FiniteBound`
 exponential winding convention (sup P,Q costs independent of torus, not asserting an
 exact equality on wrapping terms). Initialize literally the Wilson jets. No diagram
 statement by fiat (`FiniteBound` *just* thermal log Hessian program*). Solve this
 finite-order prescription in the category of summable representatives. A realization
 on a physical schedule follows from constructing one crop of formal tensors (from `Planned`
 is enough using API in this module); ***must*** show extraction independent of every
 selection on this schedule, see following modules.

 Kernel for this comparator uses physical StepData; no choice of masses based on
 answer; XSpace Rose calibration is DISTINCT and corresponding relationship still needed.
 Predictions in orientation channel gauge used by Precision, no requirement of any
 unstated soldi. Counterterms here reset coupling at each m by extracting one-loop kinetic
 projector on normalized potential, not XSpace prescription.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Compass
open Function Filter Set Precision RG Tree Wilson Lattice Work Exterior
open WilsonStartup.Change Extension.UV.LoopRate Extension.UV.StationaryData Bid
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} (A:Levels G)

/-- Maps cover the stationary working slots. Off-axis data (`m>N`) unused. -/
structure Crop where
    model : ℕ→ℕ→PathData G
    alpha : ℕ→ℕ→ℝ
    station (N m p:ℕ) (F:Forest (A.clock.op m p).ratio) : fieldDir G (A.S.side m p) 1 → AxisChart G F

namespace Crop
variable {A} (V:Crop A)

/-- Whole germ integral *prescription* not fixed memory. Coefficients after summation.
    Thermal analytic chart ratio also serves the converter/sensor's convention. -/
structure Fires (C:ChartRatio G): Prop where
   budget (N m:ℕ) : m≤N → ∃ σ C Λ, (V.model N m).Bounds (A.params m).clip σ C Λ
   summit N p : Matches 4 (AT (A.S.side N p) (A.params N).clip (V.model N N)) (fun a=> Wilson.energy (represent a)) 0
   atLoop N p : Matches 2 (L (A.S.side N p) (V.model N N)) 0 0
   each N m : m<N →
      ∃ (η γ Γ Λ:ℝ), 0<η∧ 0<γ∧∀ (p:ℕ) (F:Forest (A.clock.op m p).ratio),
        let U:=V.station N m p F; let L:=A.params (m+1); let T:=V.model N (m+1); let J:=V.model N m
        let W:=(A.params m).clip; PriceGap F L.clip T η ∧ Critical F L.clip T U ∧ ClassicalMatch F L.clip W T J U ∧
        FiniteBound F T J L.clip W (V.alpha N m) C U Γ γ Λ

-- chart-invariant
lemma compatible {C Z:ChartRatio G} (h: V.Fires C)(ht:LocalRatio C)(hu:LocalRatio Z): V.Fires Z:=by
   refine ⟨h.budget,h.summit,h.atLoop,fun N m hm=>?_⟩
   obtain ⟨η,g,k,t,hη,hg,H⟩:= h.each N m hm
   refine ⟨η,g,k,t,hη,hg,fun p F=>?_⟩
   obtain ⟨hi,hh,hF,he⟩:= H p F; exact ⟨hi,hh,hF,promos F ht hh hu he⟩

variable {C:ChartRatio G} {M:Horizon A}
def flowers (K:Kin M C):Crop A:=⟨K.path,K.alpha,K.stationary⟩
variable {s : Supply.Sheet G}{p:Supply.Rolls s}{P:PostCost p} (K:Kin M C)

lemma importsC (h:K.Planned P) : (flowers K).Fires C:=by
  refine ⟨fun n m hm=> ⟨_,_,_,h.cap _ _ hm⟩,fun N p=> ?_,fun N p=>?_,fun N m hm=> ⟨_,_,_,_,P.price _,P.posC _,fun p F=> ⟨h.gap N m p hm F,(h.critical N m p hm F).1,h.classicalPart N m p hm F,h.retains N m p hm F⟩⟩⟩
  · have he:= h.peak N p 4 le_rfl
    exact ⟨he.1,he.2.1,fun i hi=> (h.peak N p i hi).2.2⟩
  have hh:L (A.S.side N p) ((flowers K).model N N)=0:= by ext V; unfold L; simp [Precision.loop,Patch.average,uncut, Atom.unmasked, Atom.poly,h.initial,flowers]
  rw [hh]; exact matches_self _ contDiffAt_const
end Crop
-- the profile extraction
abbrev Massless (A:Levels G)(g n:ℕ) := fieldDir G (A.S.side g n) 1→ℝ

/-- profile with same jets, values always intended inclusive horizon
 together with crop declarations, no dependence on existential shooting. -/
structure Harvest where
   -- divided powers to series definitions in consumers; compare via undivided tensors first
   main (N m p i:ℕ): Tensor.T (fieldDir G (A.S.side m p) 1) ℝ i
   loop (N m p:ℕ) : Tensor.T (fieldDir G (A.S.side m p) 1) ℝ 2
   alpha (N m:ℕ) : ℝ

-- complete with zeros so no comparing arbitrary scratch.
def Crop.harvest {A:Levels G} (V:Crop A) : Harvest A:=
   ⟨fun N m p i=>if i≤4∧m≤N then iteratedFDeriv ℝ i (AT (A.S.side m p) (A.params m).clip (V.model N m)) 0 else 0,
    fun N m p=> if m≤N then iteratedFDeriv ℝ 2 (L (A.S.side m p) (V.model N m)) 0 else 0,
    fun N m=>if m<N then V.alpha N m else 0⟩

def Reaps (T:Harvest A):Prop:= ∃ C:ChartRatio G, LocalRatio C∧ ∃ V:Crop A, V.Fires C∧V.harvest=T
end YM.MatchingLedger.Compass
