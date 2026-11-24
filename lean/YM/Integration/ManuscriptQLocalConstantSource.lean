import YM.Integration.ManuscriptQLocalActualLog

/-! A spatially constant charged source passes through the full physical
conditional integral with its original coefficient. This applies to every
coarse field and keeps the signed inherited source inside the same integral. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalConstantSource

open Function Finset MeasureTheory Lattice Wilson RG Precision Marker Multi Exterior Tree
open RG3.Forms RG3.Script.Picnic LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 Integral Actual PhysicalNext.Repeat.Legato Extra.Trajectories
open Push.GridApprox
open scoped Classical BigOperators Topology

variable {V : Type} [DecidableEq V] {Γ : Census V}

/-- The physical marker integral commutes with multiplication by a fixed
signed marker polynomial, including every mixed and repeated source mode. -/
theorem charge {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → Poly Γ) (hZ : Actual.Good μ Z) (a : Poly Γ) :
    Actual.charge μ (fun u => a * Z u) = a * Actual.charge μ Z := by
  apply Marker.Poly.ext
  intro i
  have hi (p q : Γ.Mode) : Integrable
      (fun u => if Poly.merges p q i then a.part p * (Z u).part q else 0) μ := by
    by_cases h : Poly.merges p q i
    · simpa only [h,if_true] using (hZ q).const_mul (a.part p)
    · simp [h]
  simp only [Actual.components,Actual.atMark,Poly.part_mul]
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => hi p q))]
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_finsetSum _ (fun q _ => hi p q)]
  apply Finset.sum_congr rfl
  intro q _
  by_cases h : Poly.merges p q i
  · simp only [h,if_true]
    exact integral_const_mul _ _
  · simp [h]

variable {G : Gauge} {c f : Side}

/-- Fixed charged multiplication commutes with the literal physical kernel
for the same field, including on configurations of zero fine density. -/
theorem pushed (S : StepData c f) (β : ℝ) (hK : S.IsKernel β G)
    (z : Config G f → Poly Γ) (hz : Leaf.All z) (a : Poly Γ) (v : Config G c) :
    Actual.Push S β (fun u => a * z u) v = a * Actual.Push S β z v := by
  letI : IsFiniteMeasure (prior G f) :=
    inferInstanceAs (IsFiniteMeasure (Measure.pi (fun _ : Edge (Site f) => G.probHaar)))
  have he : Envelope (fun u : Config G f => S.density β u v) :=
    Envelope.comp_env (f := fun y : Config G f × Config G c => S.density β y.1 y.2)
      (g := fun u => (u,v)) (den_env hK) (measurable_id.prodMk measurable_const)
  unfold Actual.Push
  simp_rw [← mul_smul_comm]
  exact charge _ _ (Actual.Good.of_bound (prior G f) (Leaf.smul he.ofReal_env hz)) a

variable [Fintype V]

/-- The denominator of a fixed nonquiet exponential is exactly the same
original physical denominator at the given stopping field. -/
theorem normalized (a z : Poly Γ) (ha : a.part Γ.quiet=0) :
    Order.unitScale (Poly.pass a * z) = Poly.pass a * Order.unitScale z := by
  rw [Order.unitScale,Poly.quiet_mul,Poly.pass_part a ha,one_mul,Order.unitScale,mul_smul_comm]

/-- A fixed charged exponential contributes its whole signed logarithm
to the connected conditional on every field where that quotient is defined. -/
theorem connected (a z : Poly Γ) (ha : a.part Γ.quiet=0) (hz : z.part Γ.quiet≠0) :
    Extra.Trajectories.connected (Order.unitScale (Poly.pass a * z)) =
      a + Extra.Trajectories.connected (Order.unitScale z) := by
  rw [normalized a z ha,Cumulants.connected_mul (Poly.pass_part a ha)
    (Order.unitScore hz),Cumulants.connected_pass ha]

/-- Extract the constant part of an arbitrary incoming signed table before
any measurement of its labels. -/
def strip (a : Poly Γ) (z : Config G f → Poly Γ) (u : Config G f) : Poly Γ :=
  Poly.pass (-a) * z u

private theorem inverse (a : Poly Γ) (ha : a.part Γ.quiet=0) :
    Poly.pass a * Poly.pass (-a) = 1 := by
  rw [← pass_add ha (by rw [Poly.part_neg,ha,neg_zero]),add_neg_cancel,pass_zero]

theorem restore (a : Poly Γ) (ha : a.part Γ.quiet=0)
    (z : Config G f → Poly Γ) (u : Config G f) : Poly.pass a * strip a z u = z u := by
  rw [strip,← mul_assoc,inverse a ha,one_mul]

/-- Both numerator factorizations and the equality of the complete
denominators hold on the actual pushed measure. -/
theorem conditional (S : StepData c f) (β : ℝ) (hK : S.IsKernel β G)
    (z : Config G f → Poly Γ) (hz : Leaf.All z) (a : Poly Γ)
    (ha : a.part Γ.quiet=0) (v : Config G c) :
    let y := Actual.Push S β z v
    let y₀ := Actual.Push S β (strip a z) v
    y = Poly.pass a * y₀ ∧ y.part Γ.quiet = y₀.part Γ.quiet ∧
      (y.part Γ.quiet ≠ 0 → Extra.Trajectories.connected (Order.unitScale y) =
        a + Extra.Trajectories.connected (Order.unitScale y₀)) := by
  intro y y₀
  have hs : Leaf.All (strip a z) := Leaf.mul (Leaf.save _) hz
  have hy : y = Poly.pass a * y₀ := by
    have eqn : z = fun u => Poly.pass a * strip a z u := funext (fun u => (restore a ha z u).symm)
    calc
      y = Actual.Push S β (fun u => Poly.pass a * strip a z u) v :=
        congrArg (fun x => Actual.Push S β x v) eqn
      _ = _ := pushed S β hK _ hs _ v
  have hq : y.part Γ.quiet = y₀.part Γ.quiet := by rw [hy,Poly.quiet_mul,Poly.pass_part a ha,one_mul]
  refine ⟨hy,hq,?_⟩
  intro h
  rw [hy]
  exact connected a y₀ ha (hq ▸ h)

variable (R : Run G) {J : Request V} {A : NumericSchedule R.family J}
    (d : LocalFormal.Datum R.family Γ) (F : AnalyticInput J A d) (x : TestSpace J.tests)
local notation "P" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "P₀" => R.family.path.rep d.cutoff d.period d.level
local notation "Δ" => R.family.path.levels.clock.op d.level d.period
local notation "g" => Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
local notation "a₀" => F.packets.read x g 1
local notation "Π" => ManuscriptQLocalActualLog.source R d F x

private theorem quiet (U : Config G (R.family.side (d.level+1) d.period)) :
    (F.packets.read x g U).part Γ.quiet=0 := by
  classical
  let f:=fun i=>Poly.send (F.packets.mode i) (F.packets.term x g U i)
  change (∑' i,f i).part Γ.quiet=0
  by_cases hs : Summable f
  · rw [Marker.Poly.share hs]
    have h (i : ℕ) : (f i).part Γ.quiet=0 := by
      cases hi : F.packets.packet i with
      | none => simp [f,MarkedPackets.term,hi]
      | some T => simp only [f,Poly.part_send,if_neg (Ne.symm (F.packets.marked i T hi))]
    simp only [h,tsum_zero]
  · rw [tsum_eq_zero_of_not_summable hs]
    rfl

/-- On the genuine positive original vacuum the complete flat source passes
through every physical block and all independent external mark fields. -/
theorem original (v : Config G (R.family.side d.level d.period)) :
    Local.cumulant P Π Δ v =
      a₀ + Extra.Trajectories.connected (Order.unitScale (Actual.Push Δ (P).beta (strip a₀ Π) v)) := by
  have h := ManuscriptQLocalActualLog.floor R d F x
  have hv := (Local.RealStep.advance R.family d.cutoff d.period d.level d.below Π R.makes h).vacancy v
  have positive := (Normal.actual R.family.path R.makes.wilson d.cutoff d.period d.level d.below.le).positive v
  exact (conditional Δ (P).beta (R.family.path.levels.transition_mass d.level d.period (P).beta)
    Π h.safe a₀ (quiet R d F x 1) v).2.2
    (hv.trans_ne (Complex.ofReal_ne_zero.mpr positive.ne'))

/-- The centered integrand of a submitted inherited source keeps the whole
original signed remainder, with all spectator and compulsory partners. -/
theorem prepared {η : ℝ} (I : FullPreparedInputAt F η)
    (u : Config G (R.family.side (d.level+1) d.period)) :
    strip a₀ (I.input.leaf x).density u =
      Poly.pass (F.packets.read x g u - a₀) * (I.prepared.remainder.leaf x).density u := by
  calc
    _ = Poly.pass (-a₀)*(Poly.pass (F.packets.read x g u)*(I.prepared.remainder.leaf x).density u) :=
      congrArg (fun b : Poly Γ=>Poly.pass (-a₀)*b) (I.prepared.full x u)
    _ = _ := by
      rw [←mul_assoc,←pass_add (by rw [Poly.part_neg,quiet R d F x 1,neg_zero]) (quiet R d F x u)]
      congr 2
      abel

end YM.Integration.ManuscriptQLocalConstantSource
