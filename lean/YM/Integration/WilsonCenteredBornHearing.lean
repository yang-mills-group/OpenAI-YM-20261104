import YM.Integration.WilsonCenteredWatchedClasses

/-! A single small-radius gate admits every lifted physical field in the
macroscopic detector. In particular the input labels can be the reader's
actual fields at the submitted radius. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredBornHearing
open Function Set Filter Metric MeasureTheory Analysis Table Spec Lattice Extraction Next.UVStress OPE.Orbits
open Wilson RG Source PhysicalNext.Repeat.Legato StressFlux.Matching Finset Cells
open WilsonCenteredPhysicalPanel WilsonCenteredCompactBooking WilsonCenteredWatchedShape WilsonCenteredWatchedCylinder
open WilsonCenteredWatchedClasses WilsonMacroscopicRichWatchPlot WilsonMacroscopicRichWatchReader
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {n a:ℕ} {f:Extraction.Order} {S:Table R.family.book}

private theorem supported (φ : Test n) (K : Points n → ℂ) :
    (∫x in tsupport (φ : Points n→ℂ),φ x*K x)=φ.applyTo K :=by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have h : φ x = 0 :=by by_contra hn; exact hx (subset_closure hn)
  rw [h,zero_mul]

/-- Each radius is chosen before the measured classes, which may depend on
that radius. Every far tester retains its original placement and shares the
Wilson denominator with the entire near source. -/
theorem original (F:Spec.Final R.family f S) (simple:G.Simple) (φ:Test n)
    (W:Fin a→Watch R.family) :
    ∀ᶠ r:ℝ in 𝓝[>] 0, ∀ (d:Fin n→ℕ) (v:Labels S d), ∃ pred:ℕ→Prop,
      f.limits pred (fun N p=> WilsonMacroscopicRichFixedWatchSale.heard (calibrated S ∘ W) (N,p)
        (cylinder R d (N,p) (lift R d v) (mass R φ r (N,p))))
      (fun i=>φ.applyTo (fun x=> current W (r•x).ofLp v i)) :=by
  choose ρ pos geometry using fun i=>WilsonCenteredWatchedShape.original (W i) φ
  have near : ∀ᶠ r:ℝ in 𝓝[>] 0, ∀i,r<ρ i :=
    (eventually_all.mpr (fun i=>Iio_mem_nhds (pos i))).filter_mono nhdsWithin_le_nhds
  filter_upwards [near,self_mem_nhdsWithin] with r small hr
  intro d v
  have step (i:Fin a) : ∃ pred:ℕ→Prop, f.limits pred
      (fun N p=> WilsonMacroscopicRichFixedWatchSale.heard (calibrated S ∘ W) (N,p)
        (cylinder R d (N,p) (lift R d v) (mass R φ r (N,p))) i)
      (φ.applyTo (fun x=> current W (r•x).ofLp v i)) :=by
    obtain ⟨clear,loose⟩:=geometry i r hr (small i)
    let w := calibrated S (W i)
    let u := lift R d v
    let K := tsupport (φ : Points n→ℂ)
    obtain ⟨pred,adm,V,mesh,per⟩:=YM.FrontierTrace.Primary.Junction.junction_tail F
      (K:=K) (μ:=volume.restrict K) (tags R d u w) (joint w r) (φ : Points n→ℂ)
      (R.again simple).1.control (continuous_joint w r) φ.hasCompactSupport clear
      (ae_restrict_mem φ.hasCompactSupport.measurableSet) loose
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).restrict
    refine ⟨pred,adm,V,fun p hp=>?_,?_⟩
    · refine (mesh p hp).congr' ?_
      filter_upwards [f.mesh.cofinal.eventually_ge_atTop w.t] with k hk
      rw [supported]
      exact (WilsonCenteredWatchedCylinder.original R d u w φ r (p:=p) hk).symm
    · rw [supported] at per
      exact (WilsonCenteredWatchedClasses.tested R F W i d v r φ clear) ▸ per
  choose pred ordered using step
  choose V mesh vol using fun i=>(ordered i).2
  exact ⟨fun p=>∀i,pred i p,eventually_all.mpr (fun i=>(ordered i).1),
    (fun p i=>V i p),(fun p hp=>tendsto_pi_nhds.mpr (fun i=>mesh i p (hp i))),
    tendsto_pi_nhds.mpr vol⟩

end YM.Integration.WilsonCenteredBornHearing
