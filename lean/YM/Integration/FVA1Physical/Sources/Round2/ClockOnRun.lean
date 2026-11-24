import YM.Integration.FVA1Physical.Sources.Round2.PosteriorReclock
import YM.Integration.FVA1Physical.Sources.Round2.ThermalClockGain
import YM.Integration.FVA1Physical.Round2.PinnedFieldEmissions
import YM.Integration.FVA1Physical.Wilson.BankDegree

/-! On the same calibrated Wilson scene, the cutoff-independent true change of
coupling pays for inserting a mixed physical field's Wilson bank at the next
clock inside an actual normalized posterior. -/
set_option autoImplicit false
set_option maxHeartbeats 1650000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Set Finset MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior Pressure
open MSbar MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Mosaic MSbar.Bulk MSbar.Lis
open MSbar.Cacao MSbar.Measuring MSbar.Whisk MSbar.Rolling MSbar.Bakery MSbar.Bakery.Film MSbar.Bakery.Portal
open MSbar.Midpoint Extra.Histories PhysicalNext.Repeat.Legato RGComparison.Core16.Spool Push.Uniform
open PhysicalNext PhysicalNext.Repeat Push.PriceCompiler Roost Qlocal.Schedule Next.Foundations
open YM.Integration.FVA1Physical.Wilson
open scoped Classical Topology BigOperators
variable {G:Gauge} {ι:Type} [Fintype ι] (J:ι→Lamp G)

theorem emitted_same_degree (A:Issue G) (χ:ChartRatio G) (o:ι→Site A.f) (part:Bool) (p:ℕ)
    (kind:Kind A.T) (pd:(mold A.pre A.F A.v).PosDef) (plane:Expanse A.T 1 p)
    {i:ℕ} (hi:i ≤ p) :
    (PowerSeries.coeff i (emittedRows A χ (jointFieldBank J A o part) p)).totalDegree ≤ emittedDegree p := by
  have input (j:ℕ) (hj:j ≤ p) : (PowerSeries.coeff j (jointFieldBank J A o part)).totalDegree ≤ p+1+p := by
    rw [jointFieldBank,PowerSeries.coeff_mk]
    exact (MvPolynomial.totalDegree_rename_le ..).trans ((lampRow_degree J part _ j).trans (by omega))
  rw [emittedRows,PowerSeries.coeff_map]
  exact (Rolling.clearD ..).trans (normalized_input_degree A χ (jointFieldBank J A o part) p (p+1+p)
    (by omega) kind pd plane input hi)

theorem clockReading_stencil (A:Issue G) (χ:ChartRatio G) (p:ℕ) (o:ι→Site A.f) (part:Bool) (U:Config G A.c) :
    clockReading p A.fClock (emittedRows A χ (jointFieldBank J A o part) p) (chartLog A.fClock U) =
      independentStencil J A χ p o part U := by
  unfold clockReading taste picture independentStencil
  simp only [PowerSeries.coeff_map]

theorem physical_reclock_on (simple:G.Simple) (R:PhysicalNext.Repeat.Legato.Run G) (u:G.ColorIndex)
    (V:Voice G) (clear:Clear G V) (frame:R.metals.O=chart G)
    (rows:emissionInvoice J V clear simple R.metals R.rolls R.alloy R.kit)
    (inv:vacuumInvoice u V R.metals R.rolls R.alloy R.kit) (p r s L:ℕ)
    (pr:p+2 ≤ r) (hs:6 ≤ s) {D η:ℝ} (hD:0 ≤ D) (hη:0 < η) (hp:η < (p:ℝ)+1) :
    ∀ᶠ k:ℕ in atTop, ∀ N n,k ≤ N →
    ∀ (T:Scene R.family.path.levels n r) (scene:Realized R.alloy.B.kin N n k r (Lis.sun G u) T)
      (j:ℕ) (kj:k ≤ j) (jN:j<N),
      let F:=(scene.step j jN kj).choose;let v:=(scene.step j jN kj).choose_spec.choose
      let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) T F v
      let y:=R.family.path.levels.clock.hatBeta j; let z:=R.family.path.levels.clock.hatBeta (j+1)
      ∀ (b:Site A.c) (o:ι→Site A.f) (part:Bool),
      (∀ t:Slice J,separation (A.S.ratio.embed b) (legs J o t).1 ≤ L*closeN z) →
      let bank:=emittedRows A R.metals.O (jointFieldBank J A o part) p
      let price:=sourceClock (emittedDegree p) (T.action j) bank
      ∀ {c:Side} (outer:StepData c A.c) (P:Rep G A.c) (O:Config G c) {σ C δ Λ w:ℝ},
      Admitted O P outer σ C δ Λ w → ∀ (H:Set (Config G A.c)),MeasurableSet H →
      ∀ (copy:Config G A.c → Config G A.c),Measurable copy →
      (∀ U∈H,‖chartLog A.cClock (copy U)‖ ≤ D*room y/A.cClock) →
      |expect outer P O (H.indicator (independentStencil J A R.metals.O p o part ∘ copy))-
       expect outer P O (H.indicator (fun U=>clockReading p A.cClock price (chartLog A.cClock (copy U))))| ≤
        A.cClock^((p:ℝ)+1-η) := by
  let m:=emittedDegree p
  have use:=pinned_emissions J simple R u V clear frame rows inv
  have small:η/2<(p:ℝ)+1:=by linarith only [hp,hη]
  have rise:=RG01.Physical.hats simple R.family.path.levels
  obtain ⟨k₀,guard⟩:=eventually_atTop.mp (rise.eventually (thermal_reset_gain m p hD hη hp))
  filter_upwards [use p r s m L (by omega) hs 0 (η/2/16) le_rfl (by positivity),
    measured_source_on simple R u V inv p r s m m pr hs (half_pos hη) small,eventually_ge_atTop k₀]
    with k bought rate delay N n kN T scene j kj jN F v A y z b o part near bank price c outer P O σ C δ Λ w law H me copy mc live
  let Z:=RunFormalChain.fromRun R
  have seed:=(scene.budget (j+1) jN (kj.trans (Nat.le_succ j))).1
  have branch:=(R.family.path.levels.blocks j n).branches
  have pd:(mold A.pre A.F A.v).PosDef:=by
    change (Push.Uniform.block (priced F v (R.family.path.rep N n (j+1)).clip (R.family.path.rep N n (j+1)).path) 0).PosDef
    rw [Z.clips N n (j+1) jN,Z.selected N n (j+1) jN]
    exact blueprint F v (Z.kin.path N (j+1)) _ branch seed.quiet (Z.post.price _) (Z.planned.gap N j n jN F)
  have degree (i:ℕ) (hi:i≤p) : (PowerSeries.coeff i bank).totalDegree ≤ m :=emitted_same_degree J A R.metals.O o part p seed.bond pd (show Expanse A.T 1 p from ⟨fun t ht=>seed.plane.profile t (by omega)⟩) hi
  have hcard := (R.makes.wilson.represents N n j jN.le).band
  have hfine := (R.makes.wilson.represents N n (j+1) jN).band
  have yp:0<y:=zero_lt_one.trans (R.family.path.levels.fits.delayed j)
  have zp:0<z:=zero_lt_one.trans (R.family.path.levels.fits.delayed (j+1))
  have coarse:0<A.cClock:=inv_pos.mpr (Real.sqrt_pos.mpr ((half_pos yp).trans_le hcard.1))
  have fine:0<A.fClock:=inv_pos.mpr (Real.sqrt_pos.mpr ((half_pos zp).trans_le hfine.1))
  have account:=rate N n kN T scene j kj jN _ _ (Measuring.chart A.c G) {b} (αm y) bank
    (fun i hi=>(bought N n kN).2 T scene j kj jN b 0 (by simp) o near part i hi)
  have pos:0 ≤ αm y:=by unfold αm Mosaic.hatW Alto.flurry;positivity
  have first:=posterior_reclock outer P O law H me copy mc A.cClock A.fClock coarse fine
    (T.action j) bank p m s degree b pos account live
  have agree:(fun U=>clockReading p A.fClock bank (chartLog A.fClock (copy U)))=independentStencil J A R.metals.O p o part ∘ copy :=
    funext fun U=>clockReading_stencil J A R.metals.O p o part (copy U)
  dsimp only at first
  rw [agree] at first
  exact first.trans (guard j (delay.trans kj) A.cClock (Mosaic.ever yp hcard.1 hcard.2))

end YM.Integration.FVA1Physical.Round2.Curvature
