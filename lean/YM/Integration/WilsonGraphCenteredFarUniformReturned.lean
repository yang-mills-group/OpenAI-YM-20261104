import YM.Integration.WilsonGraphCenteredFarReturnedBilinear
import YM.Integration.WilsonGraphCenteredFarUniformBilinearStock
import YM.Integration.WilsonGraphCenteredFarSignedInsertion
import YM.Integration.WilsonGraphCenteredFarHeaterRate

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedUniformReturned

open Function Filter Real PowerSeries Finset Continuation Growth
open Register MS MS.Native MS.Land MS.Book MS.Book.Program
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Enh O.Score O.Canon Scale Dframe Reg.Point Jury
open YangMills YangMills.Matching YM.Answer.ContinuumLimit YM.Integration
open WilsonGraphPublishedShapeEstimate WilsonGraphPreElectedShapeEstimates
open scoped Topology BigOperators Classical

universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)
private abbrev Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev Q := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev S := _root_.IssuedBridge.PostedAppointedConversion.filed
  (Z g hg) (Q.{u} g hg).MS (Q.{u} g hg).matching (Teller.logNu 1)
private abbrev θ := ElectedMeasurement.clock
  (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)) (Z g hg)

open AppointedReturnedBilinear

private theorem formal {G : Gauge} (N : Register.WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {simple : G.Simple} {P : MS.Land.Prescription (Press.portDeck G)}
    (H : Main.Match N simple M P true) (h p k : ℕ) (hpk : p≤k) :
    ∃ F : ℝ, 0≤F ∧ ∃ a : ℕ, ∀ s≥0, ∀ (farBorn : Bool) (x : Scale.Stage 2)
    (u v : Sec G h) (t : ℝ), |t|≤1 →
    let A := Kseries N M h s
    let B := AppointedFixedBilinearCrop.secondField N M h s farBorn
    ‖AppointedSignedInsertion.value N h p x t (atColumn A k t u) (atColumn B k t v) -
      crop p t (AppointedBilinearCauchy.full N h x A B u v)‖ ≤
      (AppointedSignedInsertion.budget N h p x*‖chair G h u‖*‖chair G h v‖)*(F*|t|^(p+1)*(1+s)^a) := by
  obtain ⟨E,hE,a,paid⟩ := AppointedUniformBilinearStock.uniform N M H h p k
  refine ⟨4*E,mul_nonneg (by norm_num) hE,a,?_⟩
  intro s hs farBorn x u v t ht A B
  unfold AppointedSignedInsertion.value
  rw [AppointedFixedBilinearCrop.read N]
  refine (AppointedHighFieldCrop.expense N h p k hpk x A B u v t ht).trans ?_
  exact (mul_le_mul_of_nonneg_left (paid s hs farBorn x u v) (mul_nonneg (by norm_num) (pow_nonneg (abs_nonneg _) _))).trans_eq (by ring)

/-- The appointed two-time book on the exact transferred fields has the fixed-profile
crop price at the far heater. Both birth patterns share all their booked inputs. -/
theorem onStage (h p : ℕ) {C B : ℝ} (hC : 0 < C) (hB : 0 < B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ a : ℕ, ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ s ≥ 0,
      exp s ≤ C*(gYM g.core r)^(-B) → ∀ (farBorn : Bool) (y : Spacetime) (hy : WithLp.toLp 2 ![0,y] ∈ YM.conf 2) (u v : Sec g.core h),
      let f := r*exp s
      let t := θ.{u} g hg periods strict f
      let L := AppointedCenteredReverse.transfer.{u} g hg periods strict h r f
      let A := Kseries (Z g hg) (Q.{u} g hg).MS h s
      let V := AppointedFixedBilinearCrop.secondField (Z g hg) (Q.{u} g hg).MS h s farBorn
      ‖submitted.{u} g hg h p y t (L u) (if farBorn then v else L v) -
          crop p t (AppointedBilinearCauchy.full (Z g hg) h ⟨WithLp.toLp 2 ![0,y],hy⟩ A V u v)‖ ≤
        (AppointedSignedInsertion.budget (Z g hg) h p ⟨WithLp.toLp 2 ![0,y],hy⟩*
          ‖chair g.core h u‖*‖chair g.core h v‖)*(D*(gYM g.core r)^(p+1)*(1+s)^a) := by
  let N := Z g hg
  let M := (Q.{u} g hg).MS
  let simple := _root_.IssuedMaxwell.ElectedPrescription.simple g hg
  have toZero : Tendsto (fun r => (gYM g.core r)^(p+1)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [zero_pow (Nat.succ_ne_zero p)] using (shrink simple).pow (p+1)
  have cap := ((AppointedPhysicalWindowAndPhase.earned.{u} g hg periods strict).main 0 h hC hB).2
  obtain ⟨E,hE,b,heat⟩ := AppointedCenteredTransport.farHeaterPower.{u} g hg periods strict p hC hB
  obtain ⟨k,transport,order⟩ := ((AppointedCenteredTransport.atFarClock.{u} g hg periods strict h p hC hB).and
    (eventually_ge_atTop p)).exists
  obtain ⟨D,hD,near⟩ := transport
  obtain ⟨F,hF,a,book⟩ := formal N M (Q.{u} g hg).matching h p k order
  have goes : Tendsto (fun r => D*(gYM g.core r)^(p+1)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x:=D)).mul toZero
  refine ⟨5*D+F*E,add_nonneg (mul_nonneg (by norm_num) hD) (mul_nonneg hF hE),a+b,?_⟩
  filter_upwards [near,cap,heat,positive_g simple,goes.eventually_lt_const (show (0:ℝ)<1 by norm_num)] with
    r observed hr heating positive small
  intro s hs admitted farBorn y hy u v f t L A V
  let x : Scale.Stage 2 := ⟨WithLp.toLp 2 ![0,y],hy⟩
  let X := AppointedSignedInsertion.budget N h p x*‖chair g.core h u‖*‖chair g.core h v‖
  have hX : 0≤X := mul_nonneg (mul_nonneg (AppointedSignedInsertion.budgetNonneg N h p x) (norm_nonneg _)) (norm_nonneg _)
  let W := 5*AppointedSignedInsertion.budget N h p x*‖chair g.core h u‖*‖chair g.core h v‖
  have hW : 0 ≤ W := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (AppointedSignedInsertion.budgetNonneg N h p x)) (norm_nonneg _)) (norm_nonneg _)

  let δ := D*(gYM g.core r)^(p+1)
  have g0 := pow_nonneg positive.le (p+1)
  have d0 : 0 ≤ δ := mul_nonneg hD g0
  have hp := heating s hs admitted
  have ht : |t| ≤ 1 := hp.2
  let a0 := atColumn A k t
  have gap : ‖chairs g.core h L-chairs g.core h a0‖ ≤ δ := observed s hs admitted
  have capL : ‖chairs g.core h L‖ ≤ 2 := by
    change ‖chairs g.core h (AppointedCenteredReverse.transfer.{u} g hg periods strict h r (r*exp s))‖ ≤ 2
    rw [←(AppointedCenteredWindow.fields.{u} g hg periods strict h r s).2]
    exact (hr s hs admitted).2
  have capA : ‖chairs g.core h a0‖ ≤ 3 := by
    have tri := norm_add_le (chairs g.core h a0-chairs g.core h L) (chairs g.core h L)
    rw [sub_add_cancel,norm_sub_rev] at tri
    exact tri.trans ((add_le_add (gap.trans small.le) capL).trans_eq (by norm_num))
  have fields := AppointedSignedInsertion.bothAndOnce N h p x t ht u v L a0 δ d0 capL capA gap
  have signed :
      ‖AppointedSignedInsertion.value N h p x t (L u) (if farBorn then v else L v) -
        AppointedSignedInsertion.value N h p x t (a0 u) (atColumn V k t v)‖ ≤ W*δ := by
    cases farBorn with
    | false => exact fields.1
    | true =>
      change ‖AppointedSignedInsertion.value N h p x t (L u) v -
        AppointedSignedInsertion.value N h p x t (a0 u) (atColumn (1:Guard g.core h) k t v)‖ ≤ _
      rw [AppointedBilinearBook.farBorn]
      exact fields.2
  have formal := book s hs farBorn x u v t ht
  rw [publicStage.{u} g hg h p y hy]
  have triangle := dist_triangle
    (AppointedSignedInsertion.value N h p x t (L u) (if farBorn then v else L v))
    (AppointedSignedInsertion.value N h p x t (a0 u) (atColumn V k t v))
    (crop p t (AppointedBilinearCauchy.full N h x A V u v))
  simp only [dist_eq_norm] at triangle
  refine triangle.trans ((add_le_add signed formal).trans ?_)
  have wp : 1 ≤ (1+s)^(a+b) := one_le_pow₀ (le_add_of_nonneg_right hs)
  have one : W*δ ≤ W*D*(gYM g.core r)^(p+1)*(1+s)^(a+b) := by
    calc W*δ = (W*D*(gYM g.core r)^(p+1))*1 := by dsimp only [δ];ring
         _ ≤ _ := mul_le_mul_of_nonneg_left wp (mul_nonneg (mul_nonneg hW hD) g0)
  have two := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp.1 hF) (pow_nonneg (by linarith : 0 ≤ 1+s) a)
  exact (add_le_add one (mul_le_mul_of_nonneg_left two hX)).trans_eq (by dsimp only [X,W];rw [pow_add];ring)

end YM.FVA2.GradedFar.AppointedUniformReturned
