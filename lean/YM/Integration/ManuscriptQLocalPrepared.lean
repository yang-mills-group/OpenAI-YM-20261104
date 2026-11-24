import YM.Integration.ManuscriptQLocalConstantSource
import YM.Integration.ManuscriptQLocalSector
import YM.Integration.QLocalInheritedPhysicalInlet
import YM.Integration.ActualWilsonRegularAdjustment
import YM.Integration.ActualNormalizedLocalDensity
import YM.Integration.ActualSelectedModelEnvelope
import YM.Push.LOCAL_SPLITTING.Direct

/-! The original prepared density, including all forced partners and the
submitted analytic and calibration weights, inside the physical sector sum.
The same arbitrary signed scalar test multiplies every native source mode. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalPrepared
open Function Finset MeasureTheory Lattice Wilson RG Precision Marker Multi Exterior Tree
open Overlay RG3.Forms RG3.Script.Picnic LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 Integral Actual PhysicalNext.Repeat.Legato
open Pressure Pressure.Testing Pressure.Stores Progress.DirectedRecipe PhysicalNext PhysicalNext.Repeat
open Next SectorChange Gaussian Push.SectorMeasure
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius

private theorem deck_gauge {G : Gauge} {n : Side} {ι : Type} [DecidableEq ι] [Fintype ι]
    {Γ : Census ι} {P : Rep G n} {σ c Λ δ κ : ℝ} (hP : P.Lawful σ c Λ δ κ)
    (d : Deck Γ P) (hd : d.Active) : GaugeInvariant d.density := by
  intro t U
  have hr (i) : d.contents.ray i (gauge t U) = d.contents.ray i U :=
    congrArg (Poly.send (d.contents.rays i))
      (Push.Local.Kernel.mask_gauge P.p.threshold _ (hd.articles.regular i).symmetry t U)
  have he (i) : d.contents.each i (gauge t U) = d.contents.each i U := by
    simp only [Bands.each,Bands.tagged,hP.labels.forced.sym i t U,fun j => hd.articles.invi i j t U]
  have hp (s) : d.contents.packet s (gauge t U) = d.contents.packet s U := by
    simp only [Bands.packet,Activities.admissible,gauge_flags,he]
    split_ifs <;> rfl
  simp only [Deck.density,Deck.log,Bands.extra,Bands.cluster,hr,hp,Push.Local.Kernel.exp_invariant hP t U]

private theorem leaves {G : Gauge} {n : Side} {ι : Type} [DecidableEq ι] [Fintype ι] {Γ : Census ι}
    {Y : Config G n → Poly Γ} (hY : Envelope Y) : Leaf.All Y := by
  obtain ⟨M,hM⟩ := hY.cost
  intro a
  exact ⟨(Poly.get a).continuous.measurable.comp hY.meas,M,
    fun U => (norm_le_pi_norm (Poly.part (Y U)) a).trans (hM U)⟩

variable {G : Gauge} {V : Type} [Fintype V] [DecidableEq V] {Γ : Census V}
    (R : Run G) {J : Request V} {A : NumericSchedule R.family J} (d : LocalFormal.Datum R.family Γ)
    {F : AnalyticInput J A d} {η : ℝ} (I : FullPreparedInputAt F η) (hi : Retained.NativeIntake I)
local notation "P" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "B" => QLocalInheritedPhysicalInlet.rep I
local notation "X" => I.carrier.rep
local notation "p₁" => A.inputNorm d.level
local notation "g" => Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
local notation "δ" => QLocalInheritedPhysicalInlet.insertion I

/-- The inherited, possibly independently rebooked exponent remains gauge
invariant. The bare beta and scalar in this proof are its own. -/
theorem incoming_exponent : GaugeInvariant (X).exponent := by
  have hp := (R.makes.wilson.represents d.cutoff d.period (d.level+1) d.below).good
  have pp := ((R.T.sticks d.cutoff d.period).prices (d.level+1) (Nat.zero_le _) d.below).1.point
  let P' : Rep G (R.family.side (d.level+1) d.period) := {P with v := (X).v,beta := (X).beta}
  have he : GaugeInvariant P'.exponent := Push.Local.Kernel.exp_invariant (R:=P') ⟨hp.paths,hp.labels⟩
  have point : (X).p=(P).p := I.carrier.point.trans pp.symm
  have hr (U) : (X).exponent U = P'.exponent U + (P).activities.additive (P).p U -
        (X).activities.additive (X).p U := by
    unfold Rep.exponent
    simp only [P',I.carrier.path,I.carrier.clip,point]
    ring
  have addGI {A : Activities G (R.family.side (d.level+1) d.period)} {p : BudgetPoint}
      (h : ∀ i, GaugeInvariant (A.E i)) : GaugeInvariant (A.additive p) :=
    fun k U => tsum_congr (fun i => Push.Local.Kernel.mask_gauge p.threshold _ (h i) k U)
  intro k U
  have reg : GaugeInvariant ((P).activities.additive (P).p) := by
    exact addGI (A:=(P).activities) (p:=(P).p) fun i => (hp.labels.regular.smooth i).symmetry
  have old : GaugeInvariant ((X).activities.additive (X).p) :=
    addGI (A:=(X).activities) (p:=(X).p) fun i => (I.wellFormed.regular i).symmetry
  rw [hr (gauge k U),hr U,he k U,reg k U,old k U]

include hi

theorem weight :
    Envelope (fun U => (Real.exp (-δ U) : ℂ)) ∧
    GaugeInvariant (fun U => (Real.exp (-δ U) : ℂ)) := by
  have hp := (R.makes.wilson.represents d.cutoff d.period (d.level+1) d.below).good
  have hb := QLocalInheritedPhysicalInlet.lawful I hi hp.paths
  have hx : (X).path.Bounds (X).clip (R.family.path.levels.params (d.level+1)).width
      (R.family.path.levels.params (d.level+1)).paths (R.family.path.levels.clock.loopCap (d.level+1)) := by
    rw [I.carrier.path,I.carrier.clip]
    exact hp.paths
  have he (U) : -δ U = (X).exponent U + -(B).exponent U := by
    rw [QLocalInheritedPhysicalInlet.exponent I U]
    ring
  refine ⟨?_,fun k U => ?_⟩
  · simp_rw [he]
    exact ((ActualSelectedModelEnvelope.exponent_envelope I.wellFormed hx).add
      ((B).exponentEnv hb).neg).exp.ofReal_env
  · have moved : -δ (gauge k U)= -δ U := by
      rw [he (gauge k U),he U,incoming_exponent R d I k U,Push.Local.Kernel.exp_invariant hb k U]
    exact congrArg (fun t:ℝ=>(Real.exp t:ℂ)) moved

variable (x : IndependentTests J.tests)
local notation "x₀" => testInclusion J.tests x
local notation "L" => QLocalInheritedPhysicalInlet.carried I (pullback (testInclusion J.tests) I.prepared.remainder)

/-- The complete source algebra has finite real-regulator envelopes before
the quotient is taken. All independent slots and every forced entry remain. -/
theorem input : Leaf.All (I.input.leaf x₀).density ∧ GaugeInvariant (I.input.leaf x₀).density := by
  have hp := (R.makes.wilson.represents d.cutoff d.period (d.level+1) d.below).good
  have hb := QLocalInheritedPhysicalInlet.lawful I hi hp.paths
  let cost : Γ.Mode → ℝ := envelopeProduct F.kernelCosts
  have hL := QLocalInheritedPhysicalInlet.remainder I
  have hen : Envelope (((L).leaf x).density) := hL.full_density_envelope F.kernel_positive rfl hb x
  have hG : GaugeInvariant (((L).leaf x).density) := by
    intro k U
    rw [← restoreEnvelope_density L F.kernelCosts F.kernel_positive x (gauge k U),
      ← restoreEnvelope_density L F.kernelCosts F.kernel_positive x U]
    exact congrArg _ (deck_gauge hb ((priceNormalized cost L).leaf x) (hL.budget.active x) k U)
  have convention := F.convention.marks x₀ g
    (Local.RealStep.coupling_pos R.family d.cutoff d.period (d.level+1) R.makes d.below).ne'
  have hE : Leaf.All (fun U => Poly.pass (F.packets.read x₀ g U)) := by
    simp_rw [← convention]
    exact Leaf.sum _ _ (fun i => Leaf.smul (Leaf.atom _)
      (Leaf.pow (Integral.leaf_mark g (F.colors x₀) (F.convention.well x₀)) i))
  have hw : GaugeInvariant (fun U => Poly.pass (F.packets.read x₀ g U)) := by
    intro k U
    simp only [← convention,Integral.markedLog,fun i => (F.convention.well x₀).gauges i g k U]
  have eqn : (I.input.leaf x₀).density =
      (fun U => (Real.exp (-δ U) : ℂ) • (Poly.pass (F.packets.read x₀ g U) * ((L).leaf x).density U)) :=
    funext (QLocalInheritedPhysicalInlet.prepared I x₀)
  rw [eqn]
  exact ⟨Leaf.smul (weight R d I hi).1 (Leaf.mul hE (leaves hen)),
    fun k U => congrArg₂ (fun (s:ℂ) (Z:Poly Γ)=>s•Z) ((weight R d I hi).2 k U)
      (congrArg₂ (·*·) (hw k U) (hG k U))⟩

/-- Removing the analytic marks and all remainders leaves exactly the submitted
vacuum on every field, including every flagged background. -/
theorem quiet (U : Config G (R.family.side (d.level+1) d.period)) :
    ((I.input.leaf x₀).density U).part Γ.quiet = ((X).eval U : ℂ) := by
  let c : Γ.Mode → ℝ := envelopeProduct F.kernelCosts
  have hL := QLocalInheritedPhysicalInlet.remainder I
  have hb := QLocalInheritedPhysicalInlet.valid I hi
  have hD := ActualWilsonRegularAdjustment.deck hL.budget x rfl rfl le_rfl le_rfl le_rfl
  have h₀ := ((priceNormalized c L).leaf x).vacuum (hL.budget.active x) hD hb U
  have h₁ := priceNormalized_density_part L F.kernelCosts F.kernel_positive x U Γ.quiet
  simp [envelopeProduct,Census.quiet] at h₁
  have quiet : (((L).leaf x).density U).part Γ.quiet=((B).eval U:ℂ) := h₁.symm.trans h₀
  rw [QLocalInheritedPhysicalInlet.prepared I x₀ U,Poly.part_smul,Poly.quiet_mul,
    Poly.pass_part _ (F.packets.quiet_read x₀ g U),one_mul]
  change (Real.exp (-δ U):ℂ)*(((L).leaf x).density U).part Γ.quiet=((X).eval U:ℂ)
  rw [quiet,QLocalInheritedPhysicalInlet.density I U,Complex.ofReal_mul]

local notation "Δ" => R.family.path.levels.clock.op d.level d.period
local notation "Θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "T" => ships R.alloy.B d.cutoff d.level d.period
local notation "i₀" => R.alloy.B.a.clock.J d.level
local notation "i₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "w" => R.kit.walls i₁ i₀
local notation "b" => radiusW R.kit.rider i₁ i₀ * R.alloy.B.a.clock.threshold (d.level+1)

theorem sector (Q : Allocation G Δ Θ w) (q : Chi)
    (h : Config G (R.family.side (d.level+1) d.period) → ℂ)
    (hh : Envelope h) (hg : GaugeInvariant h) (a : Γ.Mode) :
    (Δ).push (P).beta (fun U => h U * ((I.input.leaf x₀).density U).part a) =
      Marked.paidSum T Θ P d.forest Q q R.metals.O b
        (fun U => h U * ((I.input.leaf x₀).density U).part a) := by
  have hI := input R d I hi x
  apply (ManuscriptQLocalSector.bought R d Q q).apply_push (Leaf.multiply hh (hI.1 a))
  intro k U
  exact congrArg₂ (·*·) (hg k U) (congrArg (fun z:Poly Γ=>z.part a) (hI.2 k U))

/-- The single full numerator and its own field-dependent physical
denominator after reweighting the actual bare kernel. This equality also
records the complete signed law when some vacuum values are zero. -/
theorem conditional (Q : Allocation G Δ Θ w) (q : Chi) (V₀ : Config G (R.family.side d.level d.period)) :
    let z := (I.input.leaf x₀).density
    let T₀ := Actual.Push Δ (P).beta z V₀
    let μ := (Δ).push (P).beta (fun U => ((X).eval U:ℂ)) V₀
    let p₀ : Poly Γ := Poly.inject (fun a =>
      Marked.paidSum T Θ P d.forest Q q R.metals.O b (fun U => (z U).part a) V₀)
    T₀=p₀ ∧ T₀.part Γ.quiet=μ ∧
      Extra.Trajectories.connected (Order.unitScale T₀) = Extra.Trajectories.connected (μ⁻¹ • p₀) := by
  intro z T₀ μ p₀
  have hv (a) : T₀.part a = (Δ).push (P).beta (fun U => (z U).part a) V₀ :=
    congrFun (Actual.grades ..) a
  have term (a : Γ.Mode) := congrFun (sector R d I hi x Q q (fun _ => 1) (Leaf.atom _) (fun _ _ => rfl) a) V₀
  simp only [one_mul] at term
  have he : T₀=p₀ := by ext a; exact (hv a).trans (term a)
  have hd : T₀.part Γ.quiet=μ := by
    rw [hv]; exact congrArg (fun f => (Δ).push (P).beta f V₀) (funext (quiet R d I hi x))
  exact ⟨he,hd,by rw [Order.unitScale,hd,he]⟩

/-- The source may be tested by the exact healthy-masked inherited
activities, with an independent signed amplitude at each retained address. -/
theorem inherited (Q : Allocation G Δ Θ w) (q : Chi) (A₀ : Finset ℕ) (c : ℕ → ℂ) (a : Γ.Mode) :
    let z (U : Config G (R.family.side (d.level+1) d.period)) :=
      ∑ i∈A₀, c i * ((masked (p₁).threshold (I.error.labels i).support (I.error.action i) U : ℝ) : ℂ)
    (Δ).push (P).beta (fun U => z U * ((I.input.leaf x₀).density U).part a) =
      Marked.paidSum T Θ P d.forest Q q R.metals.O b
        (fun U => z U * ((I.input.leaf x₀).density U).part a) := by
  intro z
  have hpay := I.error_paid.credit.choose_spec.1
  have row (j : ℕ) : Envelope (fun U => masked (p₁).threshold (I.error.labels j).support (I.error.action j) U) := by
    refine ⟨masked_measurable _ _ _ (I.error_paid.smooth j).borel,I.error_paid.credit.choose j,fun U => ?_⟩
    by_cases h : Healthy (p₁).threshold (I.error.labels j).support U
    · rw [masked_eq _ _ _ _ h]
      exact (hpay j).2 U h [] (Nat.zero_le _) (by simp)
    · rw [masked_ne _ _ _ _ h,norm_zero]
      exact (hpay j).1
  apply sector R d I hi x Q q z _ _ a
  · exact Leaf.amounts _ _ (fun i => Leaf.multiply (Leaf.atom _) (row i).ofReal_env)
  · intro k U
    apply Finset.sum_congr rfl
    intro i _
    rw [Push.Local.Kernel.mask_gauge _ _ (I.error_paid.smooth i).symmetry k U]


/-- The complete spatially independent marked input is restored exactly
after the physical push. The remaining signed conditional still reads
every original incoming error and compulsory contribution. -/
theorem constant (v : Config G (R.family.side d.level d.period)) :
    let a := F.packets.read x₀ g 1
    let z := (I.input.leaf x₀).density
    let z₀ := ManuscriptQLocalConstantSource.strip a z
    let y := Actual.Push Δ (P).beta z v
    let y₀ := Actual.Push Δ (P).beta z₀ v
    let μ := (Δ).push (P).beta (fun u => ((X).eval u:ℂ)) v
    y=Poly.pass a*y₀ ∧ y.part Γ.quiet=μ ∧ y₀.part Γ.quiet=μ ∧
      (μ≠0 → Extra.Trajectories.connected (Order.unitScale y) =
        a + Extra.Trajectories.connected (Order.unitScale y₀)) := by
  intro a z z₀ y y₀ μ
  have h := ManuscriptQLocalConstantSource.conditional Δ (P).beta
    (R.family.path.levels.transition_mass d.level d.period (P).beta)
    z (input R d I hi x).1 a (F.packets.quiet_read x₀ g 1) v
  have den : y.part Γ.quiet=μ := by
    change (Actual.Push Δ (P).beta z v).part Γ.quiet=_
    rw [congrFun (Actual.grades ..) Γ.quiet]
    exact congrArg (fun f => (Δ).push (P).beta f v) (funext (quiet R d I hi x))
  exact ⟨h.1,den,h.2.1.symm.trans den,fun live=>h.2.2 (den.trans_ne live)⟩

/-- For any separately selected outgoing model, its field-independent
comparison, and the remaining field-dependent connected comparison, enter
with their original signs on the same physical normalizer. -/
theorem marked_constant (M : MarkedPackets J.tests G (R.family.side d.level d.period) Γ)
    (v : Config G (R.family.side d.level d.period))
    (live : (Δ).push (P).beta (fun u => ((X).eval u:ℂ)) v ≠ 0) :
    let a := F.packets.read x₀ g 1
    let baseM := M.read x₀ g 1
    let z := (I.input.leaf x₀).density
    let y₀ := Actual.Push Δ (P).beta (ManuscriptQLocalConstantSource.strip a z) v
    Extra.Trajectories.connected (Order.unitScale (Actual.Push Δ (P).beta z v)) - M.read x₀ g v =
      (a-baseM) + (Extra.Trajectories.connected (Order.unitScale y₀) - (M.read x₀ g v-baseM)) := by
  dsimp only
  rw [(constant R d I hi x v).2.2.2 live]
  abel

end YM.Integration.ManuscriptQLocalPrepared
end
