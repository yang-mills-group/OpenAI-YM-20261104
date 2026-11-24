import YM.Integration.FVA1Physical.Wilson.MeasuredScene

/-! The full rooted norm of the first true fluctuation clock replacement,
applied to normalized Wilson coefficients already emitted by an inherited
distributed RG step. No scalar or marked coefficient bound is an input. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MvPolynomial Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Bout MSbar.Duel MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Rolling MSbar.CrossH MSbar.Measuring
open PhysicalNext.Repeat.Legato Push.Uniform MSbar.Midpoint MSbar.Bakery MSbar.Bakery.Portal MSbar.Bakery.Film
open Extra.Iteration Push.PriceCompiler PhysicalNext.Repeat.Roost Next.Foundations
open RGComparison.Core16.Spool RGComparison.Core16.Lumen YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical Topology BigOperators
variable {G:Gauge} {μ:Type} [Fintype μ] {κ:μ→Type} [∀ a,Fintype (κ a)]

theorem measured_field_reset (I:∀ a,κ a→Lamp G) {goal:Qlocal.Schedule.Goal G}
    (extra:Qlocal.Schedule.Obtainable goal) (simple:G.Simple) (cost:ℝ) (positive:0<cost) :
    ∃ (R:PhysicalNext.Repeat.Legato.Run G) (u:G.ColorIndex),
      R.family.path.levels.clock.kernel.penalty=cost ∧ goal R.metals R.rolls R.alloy R.kit ∧ R.metals.O=chart G ∧
      ∀ (p s h L:ℕ), 6 ≤ s → ∀ η:ℝ,0<η → η<(p:ℝ)+1 →
      let d:=p+1; let r:=d+1+d
      ∀ᶠ k:ℕ in atTop,∀ N n,k ≤ N → ∃ S:Scene R.family.path.levels n r,
        Realized R.alloy.B.kin N n k r (Lis.sun G u) S ∧
        ∀ j,k ≤ j → j<N → ∀ (forest:Forest (R.family.path.levels.clock.op j n).ratio)
          (bits:(R.family.path.levels.clock.op j n).Choices),
          let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S forest bits
          let x:=R.family.path.levels.clock.hatBeta j; let y:=R.family.path.levels.clock.hatBeta (j+1)
          let t:=A.cClock; let v:=A.cClock/A.fClock
          ∀ (a:μ) (part:Bool) (b:Site A.c) (o:κ a→Site A.f),
            (∀ i:Slice (I a),separation (A.S.ratio.embed b) (legs (I a) o i).1 ≤ L*closeN y) →
            let T:=emittedRows A R.metals.O (jointFieldBank (I a) A o part) d
            let E:=scalarResetRow (emittedDegree d) p (S.action j) t v T
            (∀ Z:View (Primary A.c G), taste p (picture (v•Z) T) A.fClock -
              taste p (picture Z (sourceClock (emittedDegree d) (S.action j) T)) t = MvPolynomial.eval Z E) ∧
            Vault (Measuring.chart A.c G) {b} (αm x) s h 0 E (t^((p:ℝ)+1-η)) := by
  haveI:=simple.nontrivial_color
  have dim:0<G.lieDim:=by rw [Gauge.lieDim,←G.colorIso.finrank_eq];exact Module.finrank_pos
  letI : Nonempty G.ColorIndex := ⟨⟨0,dim⟩⟩
  obtain ⟨V,clear⟩:=MSbar.Heath.vocals G
  let offer:=extra.also (Round2.Curvature.finiteInvoice (fun u:G.ColorIndex=>Qlocal.Schedule.vacuumInvoice u V)
    (fun u=>Qlocal.Schedule.vacuumInvoice_obtainable simple u V clear))
  obtain ⟨R,u,pen,⟨done,account⟩,chart,bank⟩ := all_orders_coarse_fields I offer simple cost positive
  refine ⟨R,u,pen,done,chart,?_⟩
  intro p s h L hs η hη hp d r
  filter_upwards [bank d s h L hs 0 (η/16) le_rfl (by positivity),
    measured_source_on simple R u V (account u) p r s h (emittedDegree d) (by dsimp only [r,d];omega) hs hη hp]
    with k vault pay
  intro N n kn
  obtain ⟨S,scene,rows⟩:=vault N n kn
  refine ⟨S,scene,?_⟩
  intro j kj jN forest bits A x y t v a part b o near T E
  have seed := (scene.budget (j+1) jN (by omega)).1
  have hf : 0 < A.fClock := inv_pos.mpr (Real.sqrt_pos.mpr
    ((half_pos (zero_lt_one.trans (R.family.path.levels.fits.delayed (j+1)))).trans_le
      (R.makes.wilson.represents N n (j+1) jN).band.1))
  have hc : 0 < A.cClock := inv_pos.mpr (Real.sqrt_pos.mpr
    ((half_pos (zero_lt_one.trans (R.family.path.levels.fits.delayed j))).trans_le
      (R.makes.wilson.represents N n j jN.le).band.1))
  refine ⟨?_,pay N n kn S scene j kj jN _ _ _ _ _ T ?_⟩
  · intro Z
    have deg(i:ℕ)(hi:i ≤ p):(PowerSeries.coeff i T).totalDegree ≤ emittedDegree d :=
      emitted_field_degree A R.metals.O (I a) o part d seed.bond seed.plane (by dsimp only [d];omega)
    have same : t/v=A.fClock := by dsimp only [t,v];field_simp
    rw [←same]
    exact scalar_reset_identity (emittedDegree d) p (S.action j) t v T deg Z
  intro i hi
  have row := (rows j kj jN forest bits a part b 0 (by simp) o near i (by dsimp only [d];omega)).2
  simpa only [smul_zero] using row

end YM.Integration.FVA1Physical.Wilson
