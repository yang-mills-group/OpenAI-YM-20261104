import YM.Integration.WilsonMacroscopicDetector
import YM.Integration.WilsonPhysicalExteriorFrame

/-! Recovering the true UV-normalized positive-output coordinates from
macroscopic full product measurements. The fixed detector costs no power
of the scale, and converting its output into the prescribed position
frame costs at most the output dimension plus any positive slack. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicOutputCoordinates
open Function Filter Set MeasureTheory Extraction Table
open Next.Rank OPE OPE.Orbits RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonMacroscopicDetector
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}

/-- Fix one outer physical radius before every input vector and all smaller
radii. This is the engineering price of the true prescribed output inverse. -/
theorem inverse (F : Spec.Final C f S) (J : ℝ → PhysMS.tower S) (leading : PhysMS.Leading F J)
    (H : ℕ) {θ : ℝ} (hθ : 0 < θ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r in Trace.Pilot.trail,
    ∀ x : S.Field H, ‖(J r H).symm x‖ ≤ A*r^(-(H:ℝ)-θ)*‖x‖ := by
  obtain ⟨K,hK,small⟩ := WilsonPhysicalExteriorFrame.between F H J leading θ hθ
  obtain ⟨a,ap,outer⟩ := (RG17.positiveLength.and small).exists
  let power := -(H:ℝ)-θ
  let D := (J a H).symm.toLinearMap.toContinuousLinearMap
  let A := K/(a^power)*‖D‖
  have kpos : 0 ≤ K := zero_le_one.trans hK
  have apos : 0 < a^power := Real.rpow_pos_of_pos ap _
  refine ⟨A, mul_nonneg (div_nonneg kpos apos.le) (ContinuousLinearMap.opNorm_nonneg D),?_⟩
  filter_upwards [RG17.positiveLength, (show ∀ᶠ r : ℝ in Trace.Pilot.trail,r ≤ a from
    (ge_mem_nhds ap).filter_mono nhdsWithin_le_nhds)] with r rp hr
  intro x
  have estimate := outer (r/a) ⟨div_pos rp ap,(div_le_one ap).mpr hr⟩ x
  rw [div_mul_cancel₀ _ ap.ne'] at estimate
  have size : ‖(J a H).symm x‖ ≤ ‖D‖*‖x‖ := D.le_opNorm x
  change ‖(J r H).symm x‖ ≤ A*r^power*‖x‖
  refine estimate.trans ((mul_le_mul_of_nonneg_left size (mul_nonneg kpos (Real.rpow_nonneg (div_nonneg rp.le ap.le) _))).trans_eq ?_)
  change K*(r/a)^power*(‖D‖*‖x‖)=A*r^power*‖x‖
  rw [Real.div_rpow rp.le ap.le]
  dsimp only [A]
  ring

variable {R : Run G} {V : Table R.family.book}

/-- The estimator uses only the full product in each true macroscopic
detector; the right-hand packet uses the intrinsic OPE. The determinant
cost in the moving output frame still leaves a strictly positive spatial
power (take, for example, `σ=1/2`) at every coupling order. -/
theorem original {T : Campaign R} (hG : G.Simple) (W : Campaign.Pillars R T)
    {b : ℝ} (source : FundedOriginalProperties.{u} hG b W)
    (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0 < B)
    (F : Spec.Final R.family f V) (fac : OPE.Facilities R.family f V)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower V) (leading : PhysMS.Leading F J) {A : (Bel R.family.book).Hierarchy}
    (paid : ∀ d : ℕ, ∀ᶠ r in Trace.Pilot.trail, PhysMS.Frame.obedient F A (J r) d)
    {n : ℕ} (d : Fin n → ℕ) (v : (i : Fin n) → RG17.Free R.family (d i))
    {K : Set (Points n)} (compact : IsCompact K) (apart : K ⊆ conf n)
    {g : ℝ → ℝ} (hg : Trace.Pilot.Coupling G g) (H q : ℕ) {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    ∀ᶠ r in Trace.Pilot.trail, ∀ ψ : Test n, tsupport ψ ⊆ K →
    let u : Labels V d := fun i=>J r (d i) (v i)
    ‖(J r H).symm (fromProducts F H u r ψ) - (J r H).symm (RG17.basket Q H u r ψ)‖ ≤
      ε*g r^q*r^(1-σ)*(∫ z : Points n, ‖ψ z‖) := by
  have quarter : 0 < σ/4 := div_pos hσ (by norm_num)
  obtain ⟨c,cp,conversion⟩ := inverse F J leading H quarter
  have det := WilsonMacroscopicDetector.original hG W source pace hB F fac Q J leading paid d v compact apart hg H q quarter hε
  have fixed := PhysMS.subpower_payment hg hG (c*fee F H) (σ/2) (half_pos hσ) 1 zero_lt_one 0
  filter_upwards [conversion,det,fixed,RG17.positiveLength,hg.positive] with r cost data spare rp gp
  intro ψ hs
  let u : Labels V d := fun i=>J r (d i) (v i)
  let a := fromProducts F H u r ψ
  let z := RG17.basket Q H u r ψ
  let m := ∫ s : Points n, ‖ψ s‖
  have mp : 0 ≤ m := integral_nonneg fun _=>norm_nonneg _
  have factor : r^(-(H:ℝ)-σ/4)*r^((H:ℝ)+1-σ/4) = r^(σ/2)*r^(1-σ) := by
    rw [← Real.rpow_add rp, ← Real.rpow_add rp]
    congr 1
    ring
  have bill : c*fee F H*r^(σ/2) ≤ 1 := by simpa only [pow_zero,one_mul] using spare
  change ‖(J r H).symm a-(J r H).symm z‖ ≤ ε*g r^q*r^(1-σ)*m
  rw [← map_sub]
  calc
    _ ≤ c*r^(-(H:ℝ)-σ/4)*‖a-z‖ := cost (a-z)
    _ ≤ c*r^(-(H:ℝ)-σ/4)*(fee F H*ε*g r^q*r^((H:ℝ)+1-σ/4)*m) :=
      mul_le_mul_of_nonneg_left (data ψ hs) (mul_nonneg cp (Real.rpow_nonneg rp.le _))
    _ = (c*fee F H)*(r^(-(H:ℝ)-σ/4)*r^((H:ℝ)+1-σ/4))*(ε*g r^q*m) := by ring
    _ = (c*fee F H*r^(σ/2))*(r^(1-σ)*(ε*g r^q*m)) := by rw [factor]; ring
    _ ≤ 1*(r^(1-σ)*(ε*g r^q*m)) := mul_le_mul_of_nonneg_right bill
      (mul_nonneg (Real.rpow_nonneg rp.le _) (mul_nonneg (mul_nonneg hε.le (pow_nonneg gp.le _)) mp))
    _ = _ := by ring

end YM.Integration.WilsonMacroscopicOutputCoordinates
