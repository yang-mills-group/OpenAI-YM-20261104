import YM.Integration.WilsonForestRetainedFibre

/-! Signed original and retained conditional readings in the very same local
exponential coordinates, with the exterior marginal of the old action. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonForestRetainedChart
open Function Set MeasureTheory Metric Lattice RG Wilson Tree Precision PertExtension
open PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm
open WilsonPhysicalRegisteredForestAction WilsonPhysicalLocalPlaquetteForest OriginalMarkedRunAction
open scoped Classical Topology
variable {G : Gauge} (R : Run G) {N per j : ℕ}
local notation "k" => (j+1)
local notation "op" => R.family.path.levels.clock.op j per
local notation "fine" => Config G (R.family.side k per)
local notation "coarse" => Config G (R.family.side j per)
local notation "up" => R.family.path.rep N per k
local notation "held" => WilsonHeldExteriorLaw.weight R N per j

/-- The unchanged original marginal bounds the discrepancy for every measurable
local event. This includes the intersection of overlapping source collars. -/
theorem group (T : Forest (op).ratio) (E : Finset T.Free) {d : ℕ} (interior : k<N) (A : Comparison R (p:=per) interior d)
    (S : Support (R.family.side k per)) (tails : ∀ e∈E,e.val.1∈S)
    (V : coarse) (v : (({e : T.Free | e∉E}:Set T.Free) → G.El)) (C : Set fine) (mc : MeasurableSet C) (H : fine→ℝ) (eh : Envelope H) :
    let B := approximation R (p:=per) interior d
    let a := OriginalMarkedLocalPurchase.fee R.alloy.B.a k S
      ((Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N per (k+1))^(d+1))
    let w := held V (up)
    let u := WilsonForestRetainedFibre.corrected R (N:=N) T E V B v
    let read := fun (t : fine→ℝ) => ∫ x, C.indicator t (filled (S:=op) (G:=G) T E v x) ∂Chart.physical G (↥E)
    |read (fun Y=>w Y*H Y) - read (fun Y=>u Y*H Y)| ≤ (Real.exp a-1)*read (fun Y=>w Y*|H Y|) := by
  intro B a w u read
  letI : IsProbabilityMeasure (Chart.physical G (↥E)) := by unfold Chart.physical; infer_instance
  let X := filled (S:=op) (G:=G) T E v
  obtain ⟨c,hc,mn⟩ := OriginalMarkedGibbsAction.retained_floor R interior A
  have ep := (WilsonHeldExteriorLaw.regularity R N per j interior.le V B
    (OriginalMarkedRunCovariance.keep_envelope R interior A) hc mn).1
  obtain ⟨t,ht,lower⟩ := WilsonHeldExteriorLaw.upper_floor R N per j interior.le
  obtain ⟨eq,z,hz,pp⟩ := WilsonHeldExteriorLaw.regularity R N per j interior.le V (up)
    ((up).envelope (R.makes.wilson.represents N per k interior.le).good) ht lower
  have eu : Envelope u := (ep.mul (Envelope.const (WilsonForestRetainedFibre.mass R (N:=N) T E V (up) v))).mul
    (Envelope.const (WilsonForestRetainedFibre.mass R (N:=N) T E V B v)⁻¹)
  have eabs : Envelope (fun Y => |H Y|) :=
    ⟨eh.meas.abs,eh.cost.choose,fun Y => by simpa only [Real.norm_eq_abs,abs_abs] using eh.cost.choose_spec Y⟩
  let F (f : fine→ℝ) (x : ↥E→G.El) := C.indicator f (X x)
  have fi (f : fine→ℝ) (hf : Envelope f) : Integrable (F f) (Chart.physical G (↥E)) :=
    (WilsonForestRetainedFibre.envelope R T E v (Envelope.piece mc hf (Envelope.const 0))).integrable (Chart.physical G (↥E))
  rw [←integral_sub (fi _ (eq.mul eh)) (fi _ (eu.mul eh)),←integral_const_mul]
  rw [←Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le ((fi _ (eq.mul eabs)).const_mul (Real.exp a-1))
  apply ae_of_all
  intro x
  have certified := WilsonForestRetainedFibre.original R T E interior A S tails V v x
  have bound : |w (X x)-u (X x)| ≤ (Real.exp a-1)*w (X x) :=
    OriginalMarkedRelativeMoment.deviation (hz.trans_le (pp (X x))).le certified.2.1 certified.2.2
  by_cases h : X x∈C
  · simp only [F,Set.indicator_of_mem h,Real.norm_eq_abs]
    rw [←sub_mul,abs_mul]
    exact (mul_le_mul_of_nonneg_right bound (abs_nonneg _)).trans_eq (by ring)
  · simp only [F,Set.indicator_of_notMem h,sub_self,norm_zero,mul_zero,le_refl]

/-- The only cost in replacing the true integral on an accepted local chart
by the retained action is the original omitted log oscillation times the
actual cold first moment, at this precise true held field and exterior. -/
theorem original (T : Forest (op).ratio) (E : Finset T.Free) {d : ℕ} (interior : k<N) (A : Comparison R (p:=per) interior d)
    (S : Support (R.family.side k per)) (tails : ∀ e∈E,e.val.1∈S)
    (L : Voice G) (clear : Clear G L) (P : ChartRatio G) (hp : LocalRatio P)
    (o : Site (R.family.side k per)) (D : ℕ)
    (period : 2*radius D (op).ratio.count.val < (R.family.side k per).val) {τ r : ℝ}
    (pt : 0≤τ) (pr : 0<r) (sr : r<Chart.small G P)
    (small : area D (op).ratio.count.val*τ≤L.δ) (budget : L.C*(area D (op).ratio.count.val*τ)<r)
    (locality : ∀e∈E, separation o e.val.1≤D ∧ separation o (e.val.1+step e.val.2)≤D ∧
      (op).ratio.parent e.val.1=(op).ratio.parent (e.val.1+step e.val.2))
    (V : coarse) (v : (({e : T.Free | e∉E}:Set T.Free) → G.El)) (H : fine→ℝ) (eh : Envelope H) :
    let B := approximation R (p:=per) interior d
    let a := OriginalMarkedLocalPurchase.fee R.alloy.B.a k S
      ((Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N per (k+1))^(d+1))
    let C := House.chilly (G:=G) (WilsonAxialWindow.cells o (radius D (op).ratio.count.val)) τ
    let w := held V (up)
    let u := WilsonForestRetainedFibre.corrected R (N:=N) T E V B v
    let chart := fun (t : fine→ℝ) => ∫ z in ball 0 r, Chart.jacobian P z*
      C.indicator t (filled (S:=op) (G:=G) T E v (Chart.expLinks G (↥E) z)) ∂Chart.tangent G (↥E)
    |chart (fun Y=>w Y*H Y) - chart (fun Y=>u Y*H Y)| ≤
      (Real.exp a-1)*chart (fun Y=>w Y*|H Y|) := by
  intro B a C w u chart
  have raw := group R T E interior A S tails V v C (House.bath _) H eh
  obtain ⟨c,hc,mn⟩ := OriginalMarkedGibbsAction.retained_floor R interior A
  have ep := (WilsonHeldExteriorLaw.regularity R N per j interior.le V B
    (OriginalMarkedRunCovariance.keep_envelope R interior A) hc mn).1
  obtain ⟨t,ht,lower⟩ := WilsonHeldExteriorLaw.upper_floor R N per j interior.le
  have eq := (WilsonHeldExteriorLaw.regularity R N per j interior.le V (up)
    ((up).envelope (R.makes.wilson.represents N per k interior.le).good) ht lower).1
  have eu : Measurable u := (ep.meas.mul_const _).div_const _
  have charts (f : fine→ℝ) (h : Measurable f) :
      (∫ x, C.indicator f (filled (S:=op) (G:=G) T E v x) ∂Chart.physical G (↥E)) = chart f :=
    integral L clear P hp T E o D period pt pr sr small budget locality v f h
  dsimp only at raw
  rw [charts (fun Y=>w Y*H Y) (eq.meas.mul eh.meas),
      charts (fun Y=>u Y*H Y) (eu.mul eh.meas),
      charts (fun Y=>w Y*|H Y|) (eq.meas.mul eh.meas.abs)] at raw
  exact raw

end YM.Integration.WilsonForestRetainedChart
