import YM.Integration.WilsonPhysicalRegisteredForestAction
import YM.Integration.WilsonHeldExteriorLaw
import YM.Pert.Lattice.Representatives

/-! The original positive Wilson conditional at fixed V, on the funded
plaquette box. All original free links outside the integrated set are retained
inside the signed correlated integrand. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPhysicalRegisteredForestConditional
open Function Filter Set MeasureTheory Metric Lattice RG Wilson Tree Precision PertExtension
open PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm
open WilsonPhysicalLocalPlaquetteForest WilsonPhysicalRegisteredForestAction
open scoped Classical Topology
variable {G : Gauge} (R : Run G) {N p j : ℕ}
local notation "A" => R.family.path
local notation "S" => R.family.path.levels.clock.op j p
local notation "fine" => Config G (R.family.side (j+1) p)
local notation "coarse" => Config G (R.family.side j p)

/-- The normalized Wilson expectation, averaged first over the true outside,
then its genuine local Lie algebra, including the Haar Jacobian. -/
theorem original (active : j<N) (J : Voice G) (clear : Clear G J) (P : ChartRatio G) (hp : LocalRatio P)
    (T : Forest (S).ratio) (E : Finset T.Free) (o : Site (R.family.side (j+1) p)) (D : ℕ)
    (period : 2*radius D (S).ratio.count.val < (R.family.side (j+1) p).val) {τ r : ℝ}
    (pt : 0≤τ) (pr : 0<r) (sr : r<Chart.small G P)
    (small : area D (S).ratio.count.val*τ≤J.δ) (budget : J.C*(area D (S).ratio.count.val*τ)<r)
    (locality : ∀e∈E, separation o e.val.1≤D ∧ separation o (e.val.1+step e.val.2)≤D ∧
      (S).ratio.parent e.val.1=(S).ratio.parent (e.val.1+step e.val.2))
    (V : coarse) (H : fine→ℝ) (eh : Envelope H) (inv : GaugeInvariant H) :
    let faces:=WilsonAxialWindow.cells o (radius D (S).ratio.count.val)
    let cold:=House.chilly (G:=G) faces τ
    let w:=actualConditionalDensity R.family N p j V
    actualAverage R.family (N:=N) (cold.indicator H) V =
     ∫v:( {e : T.Free | e∉E}:Set T.Free)→G.El,
       (∫x in ball 0 r, Chart.jacobian P x * cold.indicator (fun U=>w U*H U)
         (filled T E v (Chart.expLinks G (↥E) x)) ∂Chart.tangent G (↥E))
       ∂Measure.pi (fun _=>G.probHaar) := by
  dsimp only
  let faces:=WilsonAxialWindow.cells o (radius D (S).ratio.count.val)
  let cold:=House.chilly (G:=G) faces τ
  let w:=actualConditionalDensity R.family N p j V
  let event:=cold.indicator (fun U=>w U*H U)
  have mc:MeasurableSet cold:=House.bath _
  obtain ⟨c,hc,lo⟩:=WilsonHeldExteriorLaw.upper_floor R N p j active
  have ew:Envelope w := (WilsonHeldExteriorLaw.regularity R N p j active V ((A).rep N p (j+1))
    (((A).rep N p (j+1)).envelope (R.makes.wilson.represents N p (j+1) active).good) hc lo).1
  have ee:Envelope event:=Envelope.piece mc (ew.mul eh) (Envelope.const 0)
  have et:Envelope (fun u:T.Slice G=>event (T.drape u)):=
    ⟨ee.meas.comp T.continuous_drape.measurable,ee.cost.choose,fun u=>ee.cost.choose_spec (T.drape u)⟩
  letI : IsProbabilityMeasure (T.order G):=inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _:T.Free=>G.probHaar))
  have change (g : Site (R.family.side (j+1) p)→G.El) (pins : ∀i,g ((S).ratio.embed i)=1) (U:fine) : event (Lattice.gauge g U)=event U := by
    have c : Lattice.gauge (g ∘ (S).ratio.embed) V=V:=by funext e;simp [Lattice.gauge,Function.comp,pins]
    have w0:=WilsonPhysicalRegisteredLocalAction.covariant A R.makes.wilson active g U V
    rw [c] at w0
    have wf (u:fine):w u=WilsonPhysicalRegisteredLocalAction.weight A N p j u V:=by
      unfold w actualConditionalDensity WilsonPhysicalRegisteredLocalAction.weight;rw [mul_comm ((S).density ..)]
    have cg : Lattice.gauge g U∈cold ↔ U∈cold:=by simp only [cold,House.chilly,Set.mem_setOf_eq,face_gauge,G.chord_conj]
    unfold event;by_cases hu:U∈cold
    · rw [Set.indicator_of_mem (cg.mpr hu),Set.indicator_of_mem hu,wf,wf,w0,inv g U]
    · rw [Set.indicator_of_notMem (fun h=>hu (cg.mp h)),Set.indicator_of_notMem hu]
  have start:actualAverage R.family (N:=N) (cold.indicator H) V=∫U,event U ∂prior G _:=by
    apply integral_congr_ae;apply ae_of_all;intro U;by_cases h:U∈cold <;> simp [event,h,w,smul_eq_mul]
  have ms : MeasurePreserving (cut T E) (T.order G)
      ((Chart.physical G (↥E)).prod (Measure.pi fun _ : ({e : T.Free | e∉E}:Set T.Free)=>G.probHaar)) := by
    convert! measurePreserving_piEquivPiSubtypeProd (α:=fun _:T.Free=>G.El) (fun _=>G.probHaar) (·∈E) using 1
    unfold Chart.physical;congr;apply Subsingleton.elim
  letI : IsProbabilityMeasure (Chart.physical G (↥E)) := by unfold Chart.physical;infer_instance
  letI : SFinite (Chart.physical G (↥E)) := by unfold Chart.physical;infer_instance
  have it:=ms.symm.integrable_comp_of_integrable (et.integrable (T.order G))
  rw [start,T.pack event (ee.integrable _) change,← ms.symm.integral_comp']
  have fibers:=integral_prod_symm (μ:=Chart.physical G (↥E)) (ν:=Measure.pi fun _:({e:T.Free|e∉E}:Set T.Free)=>G.probHaar) _ it
  simp only [Function.comp_apply] at fibers
  rw [fibers]
  apply integral_congr_ae;apply ae_of_all;intro v
  exact integral J clear P hp T E o D period pt pr sr small budget locality v (fun U=>w U*H U) (ew.meas.mul eh.meas)

/-- These local Jacobians are genuine Haar densities of the original compact
group, with smooth perturbative normalization at zero. -/
theorem ratio (G : Gauge) : ∃ P : ChartRatio G, LocalRatio P ∧ Pert.Orb.RatioAgree P := Pert.Orb.exists_haar

end YM.Integration.WilsonPhysicalRegisteredForestConditional
