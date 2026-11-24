import YM.Frontier.Tuning.Held
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Par
/-! Measurability of held and exact unheld entries for the angular continuation. Never requires Borel off-mask analytic estimates. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Frontier.Tuning.PaletteB
open Held
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Blaze Silica Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Clutch Matter PhysicalNext.Repeat.Alabaster
open Shield Art
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k k':Finset ℕ} {R A : Rep G f} {X : Coat T F} {e f':Payload G f} {l : ℕ}
variable {a W : ℝ}{τ:ℂ}
variable {O:ChartRatio G}
variable {E:Type*}[MeasurableSpace E]
variable {V:E→ Config G c}{Y:E→ F.Slice G}{z:E→Air f G}
variable {r s p q : ℂ} (ho : ∀ i y,e i y =r*R.activities.E i y+s*A.activities.E i y)
      (ht : ∀ i y, f' i y=p*R.activities.K i y+q*A.activities.K i y) (hf : Facing R A)
variable {γ:ℝ}(hr : Intake P T X.x R) (ha : Intake P T X.x A) (hk : ShellAccess S G X.x W X.width γ) (hO:LocalRatio O)
variable (hV:Measurable V)(hY:Measurable Y)(hz:Measurable z)
local notation "B" => fun i=>drive X (V i) (Y i)
local notation "n" => fun i=>worldZ (B i) R.beta (z i)
include hr hk hV hY hz
lemma penAff (j:Stores S): Measurable fun i=> chalky (B i) (n i) ((B i).input (n i)) j + crispy (B i) j:=by
  obtain ⟨hf,hM,hQ⟩:=compassBro hr.ready hV X hY hk R.beta
  have ht:=hQ z hz; have hF := Art.entering X hV hY ht
  have hK p i {w:E → Directions G _} (he' : Measurable w) : Measurable fun t=> Vine.costs (B t) (w t) p i := by
    refine Finset.measurable_fun_sum _ fun j _=> ?_
    change Measurable fun i=> if X.selected _ _ then _ else 0; split_ifs
    · exact (((Shield.strains hr.ready hV X hY hk he' p j).norm.pow_const 2).div_const 2)
    exact measurable_const
  have hC (s) i b : Measurable fun t=> rootface (B t) (n t) ((B t).input (n t)) b s i :=
    (liftB hr.ready ((continuous_pull s (0:Site c)).measurable.comp hV) (choice s X.k) X.x b i ((continuous_pull ..).measurable.comp hF)).sub (hK _ _ ht)
  have h : Measurable fun t=> chalky (B t) (n t) ((B t).input (n t)) j := measurable_const.mul (Finset.measurable_fun_sum _ fun s _=>
    Finset.measurable_fun_sum (posted (turnStore s j) (200*X.B)) fun j _=> hC _ _ false)
  exact h.add (show Measurable fun t=> crispy (B t) j from measurable_const.mul (Finset.measurable_fun_sum _ fun s _=>
    Finset.measurable_fun_sum (posted (turnStore s j) (200*X.B)) fun j _=> hK _ _ hf))
include ha ho ht hf hO
lemma embryo (j:Head S): Measurable (fun t:E=> emberC (drive X (V t) (Y t)) R ((B t).input (n t)) (n t) (z t) O a W k τ l e f' j) :=by
  let I:=fun i=>(B i).input (n i)
  change Measurable (fun t=> emberC (B t) R (I t) (n t) (z t) O a W k τ l e f' j)
  have hh:=bornB X hk hr hO hV hY hz a l k j
  have hh':Measurable fun t=>ember (B t) a A W O (n t) (I t) (low R A • z t) k l j:=by
    have hg:=bornB X hk ha hO hV hY (Measurable.const_smul hz (low R A)) a l k j
    -- likely const_smul
    dsimp only at hg
    change Measurable (fun t=> ember (B t) a A W O (worldZ (B t) A.beta (low R A • z t)) ((B t).input (worldZ (B t) A.beta (low R A • z t))) (low R A • z t) k l j) at hg
    simp_rw [moving hf] at hg; exact hg
  rcases j with j|j|j|j
  · change Measurable fun t=> if Packets.connected S l X.B j then penGain (B t) R (I t) (n t) O τ j * stock (B t) a R W O (n t) (I t) k j else 0
    split_ifs with hv
    · change Measurable (fun t=> if Packets.connected S l X.B j then stock (B t) a R W O (n t) (I t) k j else 0) at hh
      simp_rw [if_pos hv] at hh
      have h' : Measurable fun t=> Complex.exp ((τ-(R.beta:ℂ))* (↑(-(chalky (B t) (n t) (I t) j+crispy (B t) j):ℝ):ℂ) + (X.pens j).card * (ComplexVertex.logMass O R.beta - ComplexVertex.logMass O τ)) := Complex.continuous_exp.measurable.comp ((measurable_const.mul (Complex.continuous_ofReal.measurable.comp ((penAff hr hk hV hY hz j).neg))).add measurable_const)
      exact Measurable.mul h' (Complex.continuous_ofReal.measurable.comp hh)
    exact measurable_const
  · simp_rw [mix_K (B _) R ?_ ?_ (z _) O _ _ k τ A ht hf]
    change Measurable (fun i=>sheath _ _ R _ _ j) at hh
    change Measurable (fun i=>sheath _ _ A _ _ j) at hh'
    exact (measurable_const.mul (Complex.continuous_ofReal.measurable.comp hh)).add (measurable_const.mul (Complex.continuous_ofReal.measurable.comp hh'))
  · apply (Complex.continuous_exp.measurable.comp (show Measurable (fun t=>comboLog (B t) R (I t) (n t) (z t) O a τ e j) from ?_)).sub measurable_const
    have extract {f:E→ℝ} (h:Measurable fun t=> Real.exp (f t)-1):Measurable f:= by
      exact fun s hs=> by simpa [Function.comp_def, Set.preimage] using (Real.measurable_log.comp (h.add (measurable_const (a:=1)))) hs
    have hR:=extract (show Measurable fun t=>Real.exp (Polar.logMoment (B t) a R O (n t) (I t) (z t) j)-1 from hh)
    have hA:=extract (show Measurable fun t=>Real.exp (Polar.logMoment (B t) a A O (n t) (I t) (low R A • z t) j)-1 from hh')
    rcases j with (j|j)|j
    · simp_rw [mix_log _ R (I _) _ (z _) O a τ A ho hf]
      dsimp only [Polar.logMoment,Sum.elim] at hR hA
      exact (measurable_const.mul (Complex.continuous_ofReal.measurable.comp hR)).add (measurable_const.mul (Complex.continuous_ofReal.measurable.comp hA))
    all_goals exact measurable_const.mul (Complex.continuous_ofReal.measurable.comp hR)
  exact Complex.continuous_ofReal.measurable.comp hh
lemma float (p : Molecule S): Measurable fun i=>floatC (B i) R (z i) O a W k τ l e f' p:=by
  refine Finset.measurable_fun_prod _ (fun i hi=> ?_) 
  exact embryo ho ht hf hr ha hk hO hV hY hz i
end YM.Frontier.Tuning.PaletteB
