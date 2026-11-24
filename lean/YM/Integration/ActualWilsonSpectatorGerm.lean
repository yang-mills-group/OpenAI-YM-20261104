import YM.Integration.ActualWilsonAxisSpectator

/-! The paired physical spectator has an identically zero germ on the
entire unflagged neighborhood, uniformly in every independent source test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonSpectatorGerm
open Function Set Filter Finset Lattice Wilson RG Marker Source Labels
open Extra.Histories Relay Bid Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open Comparison.RG02 PhysicalNext.Repeat.Legato ActualWilsonAxisSpectator
open ProjectorNext.Equivariance RG04B.Mark RG16.Guarding
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}

theorem dressed_clean (X : Rep G n) (i : ℕ) (U : Config G n)
    (h : flags X.p.threshold U = ∅) : dressed X i U = 0 := by
  unfold dressed
  apply (tsum_congr (g := fun _ : Finset ℕ => (0:ℂ)) ?_).trans tsum_zero
  intro s
  unfold coat
  apply if_neg
  rintro ⟨hi,hs⟩
  obtain ⟨t,ht⟩ := (X.activities.forced i).inventory_ne
  have hm : t ∈ s.biUnion (fun j => (X.activities.forced j).inventory) :=
    Finset.mem_biUnion.2 ⟨i,hi,ht⟩
  have he : s.biUnion (fun j => (X.activities.forced j).inventory) = ∅ := hs.2.trans h
  exact Finset.notMem_empty t (he ▸ hm)

variable (R : Run G) (hG : G.Simple)
    {V : Type} [Fintype V] [DecidableEq V] {B : Census V} {J : Request V}
    {A : NumericSchedule R.family J} {datum : LocalFormal.Datum R.family B}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain R.family.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta}
    {M : AnalyticOutput caps Y K F}
    (S : Chosen K I M)

/-- No bound or alignment hypothesis is needed to see the complete signed
spectator vanish on every unflagged original field of this regulator. -/
theorem clean (U : Config G (R.family.side datum.level datum.period))
    (h : flags (R.family.path.levels.budget datum.level).threshold U = ∅)
    (x : IndependentTests J.tests) (v : V) : spectator R hG S x v U = 0 := by
  let X := S.output.carrier.rep
  let W := R.family.path.rep datum.cutoff datum.period datum.level
  have hx : flags X.p.threshold U = ∅ := by
    change flags S.output.carrier.rep.p.threshold U = ∅
    rwa [S.output.carrier.point]
  have hw : flags W.p.threshold U = ∅ := by
    have hp : W.p = R.family.path.levels.budget datum.level :=
      (R.makes.wilson.represents datum.cutoff datum.period datum.level datum.below.le).vac
    rwa [hp]
  let e := ActualWilsonForcedSlots.address X
    (OriginalForcedAddresses.actual_keeper R hG datum.cutoff datum.level datum.period datum.below.le)
  change (∑' j : ℕ, _ * ((Real.exp (X.exponent U) : ℂ) * dressed X j U -
    (Real.exp (W.exponent U) : ℂ) * dressed W (e j) U)) = 0
  apply (tsum_congr (g := fun _ : ℕ => (0:ℂ)) ?_).trans tsum_zero
  intro j
  rw [dressed_clean X j U hx,dressed_clean W (e j) U hw,mul_zero,mul_zero,sub_self,mul_zero]

/-- One common open neighborhood works for all source tests and directions. -/
theorem germ :
    ∀ᶠ U : Config G (R.family.side datum.level datum.period) in 𝓝 1,
      ∀ x v, spectator R hG S x v U = 0 := by
  filter_upwards [offFlags (R.family.path.levels.budget datum.level).threshold
    (R.family.path.levels.budget datum.level).threshold_pos] with U hU
  exact clean R hG S U hU

/-- A native signed realization at any measured coordinate already realizes
the spectator at coordinate zero at precisely its original price. -/
theorem exact_coordinate (d : ℕ) (hp : R.family.ref d ≤ datum.level)
    (x : IndependentTests J.tests) (v : V) (u : R.family.label d) (r : ℝ)
    (hr : Ink R.family datum.cutoff datum.period d datum.level (spectator R hG S x v) u r) :
    u = 0 ∧ Nullity R.family datum.cutoff datum.period d datum.level (spectator R hG S x v) r := by
  let C := R.family
  let N := datum.cutoff
  let p := datum.period
  let i := datum.level
  have hi : i ≤ N := datum.below.le
  have hz : Ink C N p d i (0 : Config G (C.side i p) → ℂ) 0 0 := by
    simpa only [zero_smul, norm_zero, zero_mul] using hr.scale 0 R.makes hp hi
  obtain ⟨q,hq,hpage,hval⟩ := hr
  obtain ⟨z,hz,hpz,hvz⟩ := hz
  have he : value d N p i q =ᶠ[𝓝 1] value d N p i z := by
    filter_upwards [germ R hG S] with U hU
    rw [←hval,←hvz]
    exact hU x v
  have hr0 := (same_page R.makes hi hp hq hz he).trans hpz
  exact ⟨hpage.symm.trans hr0, q,hq,hr0,hval⟩

end YM.Integration.ActualWilsonSpectatorGerm
