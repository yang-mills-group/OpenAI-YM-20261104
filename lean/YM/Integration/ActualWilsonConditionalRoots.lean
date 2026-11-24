import YM.Integration.PhysicalWilsonConditionalRestriction
import YM.Integration.ActualWilsonTransitionSpectator
import YM.Integration.PhysicalWilsonHotIntegral

/-! Rooted mask conditioning for the full measured nonlinear Wilson law.
Every original coarse field has a strictly positive conditional incoming
density. The complete connected marked error uses only the probability of
the original missing fine event at that same coarse field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonConditionalRoots
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Marker OPE.Therm
open PhysicalNext.Repeat.Legato PhysicalWilsonConditionalRestriction
open LocalComparison LocalComparison.MarkedPackets Comparison.RG02
open scoped Topology BigOperators Classical ENNReal Matrix.Norms.Frobenius

variable {G : Gauge} (C : Family G) {N p m : ℕ} (hC : C.Makes) (hm : m<N)
local notation "fine" => Config G (C.side (m+1) p)
local notation "coarse" => Config G (C.side m p)
local notation "den" => actualConditionalDensity C N p m
local notation "op" => C.path.levels.clock.op m p
local notation "β" => C.path.β N p (m+1)

def fibre (V : coarse) : Measure fine := (prior G _).withDensity (fun U=>ENNReal.ofReal (den V U))

include hC hm in
theorem density_meas : Measurable (fun z : coarse×fine=>den z.1 z.2) := by
  have hF := ((C.path.rep N p (m+1)).envelope (hC.wilson.represents N p (m+1) hm).good).meas
  have hB := ((C.path.rep N p m).envelope (hC.wilson.represents N p m hm.le).good).meas
  exact ((((op).density_meas (C.path.levels.blocks m p).branches β).comp measurable_swap).mul
    (hF.comp measurable_snd)).div (hB.comp measurable_fst)

include hC hm in
theorem strict (V : coarse) (U : fine) : 0<den V U :=
  div_pos (mul_pos (ActualWilsonTransitionSpectator.density_pos op (C.path.levels.blocks m p).branches β U V)
    (Multi.AxisShift.chosen_positive hC.wilson hm U)) (Multi.AxisShift.chosen_positive hC.wilson hm.le V)

include hC hm in
theorem probability (V : coarse) : IsProbabilityMeasure (fibre C (N:=N) V) where
  measure_univ := by
    rw [fibre,withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
      ←ofReal_integral_eq_lintegral_ofReal (actualConditionalDensity_integrable C hC hm V)
        (Eventually.of_forall (fun U=>(strict C hC hm V U).le)),actualConditionalDensity_total C hC hm V,
      ENNReal.ofReal_one]

private theorem slice_measurable {X Y:Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (d:X×Y→ℝ) (hd:Measurable d) (x:X) : Measurable (fun y:Y=>d (x,y)) :=
  hd.comp (measurable_const.prodMk measurable_id)

private theorem density_integral {X E:Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ:Measure X) (d:X→ℝ) (hd:Measurable d) (hpos:∀x,0≤d x) (f:X→E) :
    (∫ x,f x ∂μ.withDensity (fun x=>ENNReal.ofReal (d x)))=∫ x,d x • f x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul hd.ennreal_ofReal
    (Eventually.of_forall (fun _=>ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  refine Eventually.of_forall fun x=>?_
  change (ENNReal.ofReal (d x)).toReal • f x=d x • f x
  rw [ENNReal.toReal_ofReal (hpos x)]

include hC hm in
theorem held_density_meas (V:coarse) : Measurable (fun U:fine=>den V U) :=
  slice_measurable (fun z:coarse×fine=>den z.1 z.2) (density_meas C hC hm) V

include hC hm in
theorem average {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : coarse) (f : fine→E) :
    (∫ U,f U ∂fibre C (N:=N) V)=actualAverage C (N:=N) f V :=
  density_integral (prior G _) (fun U:fine=>den V U) (held_density_meas C hC hm V)
    (fun U=>(strict C hC hm V U).le) f

include hC hm in
theorem event (E : Set fine) (hE : MeasurableSet E) (V : coarse) :
    (fibre C (N:=N) V).real E=actualAverage C (N:=N) (E.indicator (fun _ : fine=>(1:ℝ))) V := by
  letI := probability C hC hm V
  rw [←average C hC hm V,integral_indicator hE,setIntegral_const,smul_eq_mul,mul_one]

include hC hm in
theorem mass (E : Set fine) (hE : MeasurableSet E) (near : E∈𝓝 (1:fine)) (V : coarse) :
    0<(fibre C (N:=N) V).real E := by
  rw [event C hC hm E hE V,actualAverage]
  let a := E.indicator (fun _ : fine=>(1:ℝ))
  have hB (U : fine) : ‖a U‖≤1 := by by_cases h:U∈E <;>simp [a,h]
  have hf := actualAverage_integrable C hC hm (measurable_const.indicator hE).aestronglyMeasurable hB V
  have nonneg U : 0≤den V U • a U := by by_cases h:U∈E <;>simp [a,h,smul_eq_mul,(strict C hC hm V U).le]
  apply (integral_pos_iff_support_of_nonneg nonneg hf).2
  haveI : (prior G (C.side (m+1) p)).IsOpenPosMeasure := by unfold prior; infer_instance
  apply Measure.measure_pos_of_mem_nhds (prior G (C.side (m+1) p)) (x:=(1:fine))
  filter_upwards [near] with U hU
  change den V U • a U ≠ 0
  simpa only [a,Set.indicator_of_mem hU,smul_eq_mul,mul_one] using (strict C hC hm V U).ne'

include hC hm in
theorem transfer (E : Set fine) (hE : MeasurableSet E) :
    Integrable (fun V=>(fibre C (N:=N) V).real E) (scene C.path N p m) ∧
    (∫ V,(fibre C (N:=N) V).real E ∂scene C.path N p m)=(scene C.path N p (m+1)).real E := by
  let a := E.indicator (fun _ : fine=>(1:ℝ))
  have hma : Measurable a := measurable_const.indicator hE
  have hB (U : fine) : ‖a U‖≤1 := by by_cases h:U∈E <;>simp [a,h]
  have hi := actualTransport_weighted_integrable C hC hm hma.aestronglyMeasurable hB (le_refl (m+1))
  rw [actualTransport_base C hC hm] at hi
  have h₀ := actualScene_transport C hC hm hi (Nat.le_succ m)
  have h₁ := actualTransport_weighted_integrable_of_integrable C hC hm hi (Nat.le_succ m)
  rw [actualTransport_step C hC hm a (Nat.lt_succ_self m),actualTransport_base C hC hm] at h₀ h₁
  simp_rw [event C hC hm E hE]
  refine ⟨actualScene_integrable_of_weighted C hC hm.le h₁,h₀.trans ?_⟩
  change (∫ U,E.indicator (fun _ : fine=>(1:ℝ)) U ∂scene C.path N p (m+1))=_
  rw [integral_indicator hE,setIntegral_const,smul_eq_mul,mul_one]

theorem root_near {n : Side} {θ : ℝ} (hθ : 0<θ) (X : Support n) :
    (SelectedCofactorAnchoredRegister.hot (G:=G) θ X)ᶜ∈𝓝 (1:Config G n) := by
  let W (i : Face (Per n)) := {U : Config G n | G.chord (faceValue U i)<θ}
  have hO (i) : IsOpen (W i) := isOpen_lt (by unfold faceValue; fun_prop) continuous_const
  have h1 i : (1:Config G n)∈W i := by
    simpa only [W,Set.mem_setOf_eq,show faceValue (1:Config G n) i=1 by simp [faceValue,square],
      G.chord_one] using hθ
  refine mem_of_superset ((isOpen_iInter_of_finite hO).mem_nhds (Set.mem_iInter.mpr h1)) ?_
  rintro U hu ⟨z,_,hz⟩
  obtain ⟨i,_,hi⟩ := (flags_spec θ U z).mp hz
  exact (not_lt_of_ge hi.le) (Set.mem_iInter.mp hu i)

section Source
variable {V : Type} [DecidableEq V] [Fintype V] {H : Census V}
    {D : V → ComparisonDensity.Address.Orbit} {P : MarkedPackets D G (C.side (m+1) p) H}
    {q : BudgetPoint} {addr : V→Support (C.side (m+1) p)}
    {region : Comparison.Density.Testing.Region (fun i=>(D i).Mood) (C.side (m+1) p)}
    {w : V→ℝ} {g width budget : ℝ} {off slope : ℕ}
    (hP : P.Paid q addr region w g width budget off slope) (z : IndependentTests D) (cap : ℕ) (hcap : P.rankCap≤cap)

def defect (E : Set fine) (v : coarse) : Poly H :=
  Extra.Trajectories.connected (actualAverage C (N:=N) (marked P (g:=g) z) v)-
    Extra.Trajectories.connected (conditioned (fibre C (N:=N) v) E (marked P (g:=g) z))

include hP hcap in
include hC hm in
theorem measured (X : Support (C.side (m+1) p)) {θ : ℝ} (hθ : 0<θ) :
    let B := uniformModelCost cap (Fintype.card V) budget
    let E := SelectedCofactorAnchoredRegister.hot (G:=G) θ X
    (∀ v : coarse,0<(fibre C (N:=N) v).real Eᶜ) ∧
    (∫ v,Poly.price w (defect C (N:=N) (P:=P) (g:=g) z E v) ∂scene C.path N p m)≤
      Order.repeats (Fintype.card V) (1+B)*(2*B)*(scene C.path N p (m+1)).real E := by
  intro B E
  have hE := SelectedCofactorAnchoredRegister.measurable (G:=G) θ X
  have pos v := mass C hC hm Eᶜ hE.compl (root_near hθ X) v
  refine ⟨pos,?_⟩
  have hν := transfer C hC hm E hE
  have bound (v : coarse) : Poly.price w (defect C (N:=N) (P:=P) (g:=g) z E v) ≤
      (Order.repeats (Fintype.card V) (1+B)*(2*B))*(fibre C (N:=N) v).real E := by
    letI := probability C hC hm v
    have h := PhysicalWilsonConditionalRestriction.packet P hP z cap hcap (fibre C (N:=N) v) E hE (pos v)
    simpa only [defect,average C hC hm,mul_assoc] using h
  apply (integral_mono_of_nonneg (Eventually.of_forall (fun _=>Poly.nonnegative hP.positive _))
    (hν.1.const_mul _) (Eventually.of_forall bound)).trans_eq
  rw [integral_const_mul,hν.2]

end Source
end YM.Integration.ActualWilsonConditionalRoots
end
