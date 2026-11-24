import YM.Integration.WilsonJointMoment

/-! Borel representatives for forward physical conditional readouts. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonForwardMeasurable
open Function MeasureTheory Lattice Wilson RG
open scoped Topology
variable {G : Gauge} {C : Family G} {N p m : ℕ}

private theorem scaled {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    {k : T × X → ℝ} {f : T → ℝ} {w : X → ℝ} {g : T → ℂ}
    (hk : Measurable k) (hf : Measurable f) (hw : Measurable w) (hg : Measurable g) :
    Measurable (fun z : T × X => (k z*f z.1/w z.2) • g z.1) :=
  ((hk.mul (hf.comp measurable_fst)).div (hw.comp measurable_snd)).smul (hg.comp measurable_fst)

theorem average (hC : C.Makes) (hm : m<N) {g : Config G (C.side (m+1) p) → ℂ}
    (hg : Envelope g) : Envelope (actualAverage C (N:=N) g : Config G (C.side m p) → ℂ) := by
  let P := C.path.rep N p m
  let F := C.path.rep N p (m+1)
  let K := C.path.levels.clock.op m p
  let b := C.path.β N p (m+1)
  have h : Measurable (fun z : Config G (C.side (m+1) p) × Config G (C.side m p) =>
      (actualConditionalDensity C N p m z.2 z.1) • g z.1) :=
    scaled (k:=fun z => K.density b z.1 z.2) (f:=F.eval) (w:=P.eval) (g:=g)
      (C.path.levels.transition_mass m p b).meas
      (F.envelope (hC.wilson.represents N p (m+1) hm).good).meas
      (P.envelope (hC.wilson.represents N p m hm.le).good).meas hg.meas
  obtain ⟨a,ha⟩ := hg.cost
  exact ⟨h.stronglyMeasurable.integral_prod_left'.measurable,a,actualAverage_norm_le C hC hm ha⟩
end YM.Integration.WilsonForwardMeasurable
