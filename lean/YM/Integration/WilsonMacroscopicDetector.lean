import YM.Integration.WilsonMacroscopicExteriorMeasurement

/-! A fixed macroscopic numerical estimate of the actual measured output.
Its data are only signed full-product observations at the original finite
separating family. It does not use the target packet in the estimator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicDetector
open Function Filter Finset Set MeasureTheory Extraction Table
open Next.Rank OPE OPE.Orbits RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}

def probes (F : Spec.Final C f S) (H : ℕ) : Finset (RG17.External C S) :=
  (RG17.finiteProbes F H).choose

def read (F : Spec.Final C f S) (H : ℕ) : S.Field H →ₗ[ℂ] (probes F H → ℂ) :=
  LinearMap.pi fun X : probes F H => X.val.charge F H

private theorem left (F : Spec.Final C f S) (H : ℕ) :
    ∃ A : (probes F H → ℂ) →L[ℂ] S.Field H, ∀ x, A (read F H x)=x := by
  obtain ⟨c,_,bound⟩ := (RG17.finiteProbes F H).choose_spec
  have ker : (read F H).ker=⊥ := LinearMap.ker_eq_bot'.mpr fun x hx => by
    have hz : ∑ X ∈ probes F H, ‖X.charge F H x‖=0 := by
      apply Finset.sum_eq_zero
      intro X hX
      have e : X.charge F H x=0 := congr_fun hx ⟨X,hX⟩
      rw [e, norm_zero]
    have paid := bound x
    change ‖x‖ ≤ c*∑ X ∈ probes F H, ‖X.charge F H x‖ at paid
    rw [hz,mul_zero] at paid
    exact norm_eq_zero.mp (le_antisymm paid (norm_nonneg _))
  obtain ⟨A,hA⟩ := (read F H).exists_leftInverse_of_injective ker
  exact ⟨A.toContinuousLinearMap,fun x=>LinearMap.congr_fun hA x⟩

def restore (F : Spec.Final C f S) (H : ℕ) : (probes F H → ℂ) →L[ℂ] S.Field H :=
  (left F H).choose

theorem exact_read (F : Spec.Final C f S) (H : ℕ) (x : S.Field H) :
    restore F H (read F H x)=x := (left F H).choose_spec x

def fee (F : Spec.Final C f S) (H : ℕ) : ℝ :=
  ‖restore F H‖ * ∑ X : probes F H, ∫ z : Points (X.val.n+1), ‖X.val.test z‖

/-- Numerical estimator, using only full-product data. -/
def fromProducts (F : Spec.Final C f S) (H : ℕ) {n : ℕ} {d : Fin n → ℕ} (u : Labels S d)
    (r : ℝ) (ψ : Test n) : S.Field H :=
  restore F H (fun X : probes F H=>RG17.appeared F u X.val r ψ)

variable {R : Run G} {V : Table R.family.book}

/-- A fixed finite physical detector recovers the true continuum OPE output
from the signed full products. Its norm price depends only on F and H. -/
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
    ‖fromProducts F H u r ψ - RG17.basket Q H u r ψ‖ ≤
      fee F H * ε*g r^q*r^((H:ℝ)+1-σ)*(∫ z : Points n, ‖ψ z‖) := by
  let m (X : probes F H) := ∫ z : Points (X.val.n+1), ‖X.val.test z‖
  have hm (X : probes F H) : 0 ≤ m X := integral_nonneg fun _=>norm_nonneg _
  have measurements := eventually_all.mpr fun X : probes F H =>
    WilsonMacroscopicExteriorMeasurement.signed hG W source pace hB F fac Q J leading paid d v X.val compact apart hg H q hσ hε
  filter_upwards [measurements,RG17.positiveLength,hg.positive] with r obs rp gp
  intro ψ hs
  let u : Labels V d := fun i=>J r (d i) (v i)
  let packet := RG17.basket Q H u r ψ
  let xs := fun X : probes F H=>RG17.appeared F u X.val r ψ
  let y := ∫ z : Points n, ‖ψ z‖
  let p := ε*g r^q*r^((H:ℝ)+1-σ)
  have yp : 0 ≤ y := integral_nonneg fun _=>norm_nonneg _
  have pp : 0 ≤ p := mul_nonneg (mul_nonneg hε.le (pow_nonneg gp.le _)) (Real.rpow_nonneg rp.le _)
  have price : ‖xs-read F H packet‖ ≤ (∑ X : probes F H,m X)*(p*y) := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg fun X _=>hm X) (mul_nonneg pp yp))).mpr
    intro X
    have h : ‖xs X-(read F H packet) X‖ ≤ p*m X*y := obs X ψ hs
    calc
      _ ≤ p*m X*y := h
      _ = m X*(p*y) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun z _=>hm z) (Finset.mem_univ X)) (mul_nonneg pp yp)
  have identity : fromProducts F H u r ψ-packet = restore F H (xs-read F H packet) := by
    rw [map_sub,exact_read]
    rfl
  change ‖fromProducts F H u r ψ-packet‖ ≤ fee F H * ε*g r^q*r^((H:ℝ)+1-σ)*y
  rw [identity]
  exact ((restore F H).le_opNorm _).trans ((mul_le_mul_of_nonneg_left price (norm_nonneg _)).trans_eq (by
    dsimp only [fee,p,y,m]
    ring))

end YM.Integration.WilsonMacroscopicDetector
