import YM.Integration.WilsonPhysicalHistoryRetainedSpringReading
import YM.Integration.WilsonPhysicalHistoryRetainedExterior

/-! Insert the whole authentic running-coupling remainder in both original E6
affine integrals. Its finite torus budget is selected before forest or field. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open LocalComparison Marker Global FullQLocal Comparison.RG02 Comparison.RG02.Assembly
open IterationFour IterationFour.Vacuum
open Function Filter Finset Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree MeasureTheory
open ConnectedActivityE6 ConnectedActivityE6.Coat
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure
open Bloch Laurent RG.Supply Extra.Histories GapsLocal.Renew
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Opera
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open scoped Topology BigOperators Classical
variable {G : Gauge}

theorem cofinal_spring (R : Run G) (simple : G.Simple) (held : WilsonFundedWindowCompany.PhysicalInputs R.kit)
    (mark : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (checkoutPrice : Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay) (d : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ N n : ℕ, (hq : m+1<N) →
      let A:=R.alloy.B.a
      let k:=A.clock.J (m+1)
      let j:=A.clock.J m
      let P:=R.family.path.rep N n (m+1)
      let Q:=approximation R (p:=n) hq d
      let δ:=(Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N n (m+2))^(d+1)
      let S:=A.clock.op m n
      let T:=Pressure.Testing.ships R.alloy.B N m n
      let D:=R.kit.target k j
      let W:=R.kit.walls k j
      let a:=(R.kit.shape.o k j).a
      ∃ (H : Guide R.alloy.B R.kit.shape N m n P) (b : ℕ→ℝ),
        (∀ v,SumBudget (fun i=>if (P.activities.reg i).site=v then P.p.mass (P.activities.reg i).support (b i) else 0) δ) ∧
        ∀ {r : ℕ} (V : Plan R.family N n r) {point : BudgetPoint} {cap : ℕ} {width budget : ℝ},
          GradedVacuumLayers (V.layers (m+1)) point r cap width budget → 0<width →
          ∃ K : ℝ, 0≤K ∧
          ∀ {F : Forest S.ratio} (X : Coat T F), X.x=A.clock.hatBeta m → X.width=(R.kit.shape.o k j).K → X.manifest →
          ∀ (l : Finset ℕ) (p : Molecule S) (f : F.Slice G × Air (R.family.side (m+1) n) G→ℂ),
            Measurable f → ∀ M : ℝ, 0≤M → (∀ t,‖f t‖≤M) →
            let g:=Pert.Asymptotics.regulatorRun R.family N n (m+1)
            let obs:=fun t : F.Slice G × Air (R.family.side (m+1) n) G=>
              f t * (springReading R V (m+1) g
                ((X.wrapY t.1).input ((X.wrapY t.1).liftA P.beta t.2)):ℂ)
            let err:=fun v : Head S=>(5/2:ℝ)*regularFee S b v
            let ν:=(F.order G).prod X.dice
            ‖(∫ t,obs t*(X.body P D.table W a l D.halo p t:ℂ) ∂ν)-
              ∫ t,obs t*(X.body Q D.table W a l D.halo p t:ℂ) ∂ν‖ ≤
              (M*K)*(H.alarms^(blaze p).card*insertedCost (fun v=>H.fair v+err v) err p.toList) := by
  filter_upwards [cofinal_tested R simple held mark checkoutPrice d] with m received
  intro N n hq
  dsimp only
  obtain ⟨H,b,quota,paid⟩:=received N n hq
  refine ⟨H,b,quota,?_⟩
  intro r V point cap width budget layers pos
  let g:=Pert.Asymptotics.regulatorRun R.family N n (m+1)
  have gp : 0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson hq.le))
  have spring:=spring_envelope R simple V hq gp.ne' layers pos
  obtain ⟨K,cost⟩:=spring.cost
  have nonneg:0≤K:= (norm_nonneg _).trans (cost 1)
  refine ⟨K,nonneg,?_⟩
  intro F X clock size live l p f fm M mpos bound
  have access:=H.laws.data.access
  rw [←clock,←size] at access
  have intake:=H.laws.intake
  rw [←clock] at intake
  let z (t : F.Slice G × Air (R.family.side (m+1) n) G):=(X.wrapY t.1).liftA (R.family.path.rep N n (m+1)).beta t.2
  have zm : Measurable z := (X.airwards access intake.ready measurable_fst).2.2 _ measurable_snd
  have field:=X.summon measurable_fst zm
  apply paid X clock size live l p _ (fm.mul (Complex.continuous_ofReal.measurable.comp (spring.meas.comp field)))
    _ (mul_nonneg mpos nonneg)
  intro t
  change ‖f t*(springReading R V (m+1) g ((X.wrapY t.1).input (z t)):ℂ)‖≤M*K
  rw [norm_mul,Complex.norm_real]
  exact mul_le_mul (bound t) (cost _) (norm_nonneg _) mpos

end YM.Integration.OriginalMarkedRunAction
