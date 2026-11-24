import YM.Integration.WilsonGraphCenteredFarCompactBilinearKernel
import YM.Integration.WilsonGraphCenteredFarUniformReturned
import YM.Integration.WilsonGraphCenteredFarUniformClockBill

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedNearClockBilinear
open Function Filter Real PowerSeries Finset Continuation Growth
open Register MS MS.Native MS.Land MS.Book MS.Book.Program
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Enh O.Score O.Canon Scale Dframe Reg.Point Jury
open YangMills YM.Answer.ContinuumLimit YM.Integration
open scoped Topology BigOperators Classical
universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)
private abbrev Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev Q := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev θ := ElectedMeasurement.clock
  (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)) (Z g hg)

/-- The two-time public crop, at its physical far heater and with all its actual occupied
fields, has a uniform near-clock replacement on a compact set of separated centered pairs. -/
theorem onCompact (h p : ℕ) (K : Set (YangMills.Points 2)) (compact : IsCompact K)
    (safe : K ⊆ YM.conf 2) {C B : ℝ} (hC : 0<C) (hB : 0<B) :
    ∃ D : ℝ, 0≤D ∧ ∃ a : ℕ, ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ s≥0, exp s≤C*(gYM g.core r)^(-B) →
      ∀ (farBorn : Bool) (y : Spacetime) (hy : WithLp.toLp 2 ![0,y] ∈ K) (u v : Sec g.core h),
      let f := r*exp s
      let L := AppointedCenteredReverse.transfer.{u} g hg periods strict h r f
      let A := Kseries (Z g hg) (Q.{u} g hg).MS h s
      let V := AppointedFixedBilinearCrop.secondField (Z g hg) (Q.{u} g hg).MS h s farBorn
      let ψ := GroupS.ψ (Z g hg).criterion (Q.{u} g hg).MS (Teller.logNu 1) (-s)
      let F := AppointedBilinearCauchy.full (Z g hg) h ⟨WithLp.toLp 2 ![0,y],safe hy⟩ A V u v
      ‖AppointedReturnedBilinear.submitted.{u} g hg h p y (θ.{u} g hg periods strict f)
          (L u) (if farBorn then v else L v) - crop p (θ.{u} g hg periods strict r) (F.subst ψ)‖ ≤
        ‖chair g.core h u‖*‖chair g.core h v‖*(D*(gYM g.core r)^(p+1)*(1+s)^a) := by
  let N := Z g hg
  let simple := _root_.IssuedMaxwell.ElectedPrescription.simple g hg
  obtain ⟨R,hR,kernel⟩ := AppointedCompactBilinearKernel.onCompact g hg h p K compact safe
  obtain ⟨E,hE,b,fields⟩ := AppointedUniformReturned.onStage.{u} g hg periods strict h p hC hB
  obtain ⟨D,hD,a,clock⟩ := AppointedUniformClockBill.onStage.{u} g hg periods strict h p hC hB
  refine ⟨R*(E+D),mul_nonneg hR (add_nonneg hE hD),b+a,?_⟩
  filter_upwards [fields,clock,positive_g simple] with r compared substituted positive s hs upper
  intro farBorn y hy u v f L A V ψ F
  let x : Scale.Stage 2 := ⟨WithLp.toLp 2 ![0,y],safe hy⟩
  let z := (gYM g.core r)^(p+1)
  have hz : 0≤z := pow_nonneg positive.le _
  let U := ‖chair g.core h u‖*‖chair g.core h v‖
  have hu : 0≤U := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  let X := AppointedSignedInsertion.budget N h p x*‖chair g.core h u‖*‖chair g.core h v‖
  have hx : X≤R*U := by
    calc X = AppointedSignedInsertion.budget N h p x*U := by dsimp only [X,U];ring
         _ ≤ _ := mul_le_mul_of_nonneg_right (kernel y hy) hu
  have base : 1≤1+s := le_add_of_nonneg_right hs
  have bg (q : ℕ) (leq : q≤b+a) (d : ℝ) (hd : 0≤d) :
      X*(d*z*(1+s)^q)≤(R*U)*(d*z*(1+s)^(b+a)) := by
    exact mul_le_mul hx (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ base leq) (mul_nonneg hd hz))
      (mul_nonneg (mul_nonneg hd hz) (pow_nonneg (zero_le_one.trans base) _)) (mul_nonneg hR hu)
  have c := compared s hs upper farBorn y (safe hy) u v
  have d := substituted s hs upper farBorn x u v
  have triangle := dist_triangle
    (AppointedReturnedBilinear.submitted.{u} g hg h p y (θ.{u} g hg periods strict f) (L u) (if farBorn then v else L v))
    (crop p (θ.{u} g hg periods strict f) F)
    (crop p (θ.{u} g hg periods strict r) (F.subst ψ))
  simp only [dist_eq_norm] at triangle
  exact triangle.trans ((add_le_add (c.trans (bg b (by omega) E hE)) (d.trans (bg a (by omega) D hD))).trans_eq (by dsimp only [U,z];ring))

end YM.FVA2.GradedFar.AppointedNearClockBilinear
