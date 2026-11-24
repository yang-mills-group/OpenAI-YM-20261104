import YM.Integration.WilsonPhysicalHistoryRetainedIntegral
import YM.Integration.WilsonPhysicalHistoryRetainedCourse

/-! The original cutoff-dependent external field can stay inside both
normalized shared affine averages of the received and retained molecules. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Finset Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree MeasureTheory
open ConnectedActivityE6 ConnectedActivityE6.Coat
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure
open Bloch Laurent RG.Supply Extra.Histories GapsLocal.Renew
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Opera
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open scoped Topology BigOperators Classical
variable {G : Gauge}

private theorem observed {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) {A B : Ω→ℝ}
    (first : Integrable A ν) (second : Integrable B ν) {e : ℝ} (paid : ∫ t,|A t-B t| ∂ν ≤ e)
    (f : Ω→ℂ) (meas : Measurable f) (b : ℝ) (nonneg : 0≤b) (bound : ∀ t,‖f t‖≤b) :
    ‖(∫ t,f t*(A t:ℂ) ∂ν) - ∫ t,f t*(B t:ℂ) ∂ν‖≤b*e := by
  have top:=first.ofReal.bdd_mul meas.aestronglyMeasurable (Eventually.of_forall bound)
  have low:=second.ofReal.bdd_mul meas.aestronglyMeasurable (Eventually.of_forall bound)
  have equal : (∫ t,f t*(A t:ℂ) ∂ν)-(∫ t,f t*(B t:ℂ) ∂ν) =
      ∫ t,f t*(A t:ℂ)-f t*(B t:ℂ) ∂ν := (integral_sub top low).symm
  refine (congrArg norm equal).trans_le ?_
  apply (norm_integral_le_integral_norm _).trans
  have invoice : Integrable (fun t=>b*|A t-B t|) ν := (first.sub second).norm.const_mul b
  refine (integral_mono_of_nonneg (Eventually.of_forall fun _=>norm_nonneg _) invoice (Eventually.of_forall ?_)).trans ?_
  · intro t
    change ‖f t*(A t:ℂ)-f t*(B t:ℂ)‖≤b*|A t-B t|
    rw [←mul_sub,←Complex.ofReal_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (bound t) (abs_nonneg _)
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left paid nonneg

theorem cofinal_tested (R : Run G) (simple : G.Simple) (held : WilsonFundedWindowCompany.PhysicalInputs R.kit)
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
        ∀ {F : Forest S.ratio} (X : Coat T F), X.x=A.clock.hatBeta m → X.width=(R.kit.shape.o k j).K → X.manifest →
        ∀ (l : Finset ℕ) (p : Molecule S) (f : F.Slice G × Air (R.family.side (m+1) n) G→ℂ),
          Measurable f → ∀ K : ℝ, 0≤K → (∀ t,‖f t‖≤K) →
          let err:=fun v : Head S=>(5/2:ℝ)*regularFee S b v
          let ν:=(F.order G).prod X.dice
          ‖(∫ t,f t*(X.body P D.table W a l D.halo p t:ℂ) ∂ν)-
            ∫ t,f t*(X.body Q D.table W a l D.halo p t:ℂ) ∂ν‖ ≤
            K*(H.alarms^(blaze p).card*insertedCost (fun v=>H.fair v+err v) err p.toList) := by
  have check:=(tendsto_add_atTop_nat 1).eventually (calendar R simple mark checkoutPrice d)
  filter_upwards [cofinal_integral R simple held mark checkoutPrice d,check,physical_window R simple] with m paid recvd window
  intro N n hq
  dsimp only
  obtain ⟨H,b,quota,price⟩:=paid N n hq
  refine ⟨H,b,quota,?_⟩
  intro F X clock width mf l p f meas K nonneg bound
  have front:=H.integrated X clock width mf l p
  have back:=(retained_integrable R hq (recvd N n hq) H X clock width mf ((window N n hq).2.2 d) l p).2
  exact observed _ front back (price X clock width mf l p) f meas K nonneg bound

end YM.Integration.OriginalMarkedRunAction
