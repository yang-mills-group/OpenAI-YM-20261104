import YM.Integration.WilsonGraphCenteredPhysicalPairPrice
import YM.Integration.WilsonGraphCenteredFarReturnedBilinear
import YM.Integration.WilsonGraphCenteredFarTwoClocks

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedCenteredPhysicalReturn

open Filter Real Growth Continuation
open Register MS MS.Native MS.Land MS.Book MS.Book.Program
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Enh O.Score O.Canon Scale Dframe Reg.Point
open YangMills YM.Answer.ContinuumLimit YM.Integration
open scoped Topology BigOperators Classical

universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)
private abbrev V := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)
private abbrev Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev Q := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev H := Elected.Hframe (Z g hg) (V.{u} g hg periods strict).pupil.last
  (V.{u} g hg periods strict).pupil.J
private abbrev publicTable := YangMills.hierarchy (g := g) (V.{u} g hg periods strict).pupil.last
  (V.{u} g hg periods strict).pupil.P
private abbrev heat := ElectedMeasurement.clock (V.{u} g hg periods strict) (Z g hg)

/-- The original continuum pair and the mixed continuum reading are compared with
their independently returned crops at the birth heater of the center. -/
def PairAtNearClock (h p : ℕ) (K : Set (YangMills.Points 2)) (safe : K ⊆ YM.conf 2) (C B : ℝ) : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧ ∃ e : ℕ, ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ s ≥ 0, exp s ≤ C*(gYM g.core r)^(-B) →
    ∀ (u v : Sec g.core h) (phase : Option (publicTable.{u} g hg periods strict).Character)
      (o : Spacetime) (y : YM.Points 1) (hy : (WithLp.toLp 2 ![0,y 0] : YangMills.Points 2) ∈ K),
      let w : Window := (r,s)
      let f := r * exp s
      let site : Scale.Stage 2 := ⟨WithLp.toLp 2 ![0,y 0],safe hy⟩
      let psi := GroupS.ψ (Z g hg).criterion (Q.{u} g hg).MS (Teller.logNu 1) (-s)
      let A := AppointedCenteredReverse.reverseSeries (Z g hg) (Q.{u} g hg).MS h s
      let cost := D*(‖chair g.core h u‖*‖chair g.core h v‖)*(gYM g.core r)^(p+1)*(1+s)^e
      ‖Physical.Y0 (V.{u} g hg periods strict).pupil.last (H.{u} g hg periods strict)
          (fun _ : Fin 1 => h) (fun _ : Fin 1 => h) w (phase,o) (0 : YM.Points 1) y
          (fun _ => u) (fun _ => v) -
        crop p (heat.{u} g hg periods strict r) (AppointedTwoClocks.pulled (Z g hg) h site psi A A u v)‖ ≤ cost ∧
      ‖Physical.Dactual (V.{u} g hg periods strict).pupil.last (H.{u} g hg periods strict)
          r f (phase,o) y (e := fun _ : Fin 1 => h) (fun _ => v) u -
        crop p (heat.{u} g hg periods strict r) (AppointedTwoClocks.pulled (Z g hg) h site psi A 1 u v)‖ ≤ cost

private theorem join {x y z : ℂ} {D E m t b : ℝ} {i j : ℕ}
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hm : 0 ≤ m) (ht : 0 ≤ t) (hb : 1 ≤ b)
    (left : ‖x-y‖ ≤ D*m*t*b^i) (right : ‖y-z‖ ≤ m*(E*t*b^j)) :
    ‖x-z‖ ≤ (D+E)*m*t*b^(i+j) := by
  have h0 : 0 ≤ b := zero_le_one.trans hb
  have hi : b^i ≤ b^(i+j) := by
    rw [pow_add]
    exact le_mul_of_one_le_right (pow_nonneg h0 _) (one_le_pow₀ hb)
  have hj : b^j ≤ b^(i+j) := by
    rw [add_comm i j,pow_add]
    exact le_mul_of_one_le_right (pow_nonneg h0 _) (one_le_pow₀ hb)
  calc
    ‖x-z‖ ≤ ‖x-y‖ + ‖y-z‖ := norm_sub_le_norm_sub_add_norm_sub x y z
    _ ≤ D*m*t*b^i + m*(E*t*b^j) := add_le_add left right
    _ = D*m*t*b^i + E*m*t*b^j := by ring
    _ ≤ D*m*t*b^(i+j) + E*m*t*b^(i+j) :=
      add_le_add (mul_le_mul_of_nonneg_left hi (mul_nonneg (mul_nonneg hD hm) ht))
        (mul_le_mul_of_nonneg_left hj (mul_nonneg (mul_nonneg hE hm) ht))
    _ = (D+E)*m*t*b^(i+j) := by ring

/-- The two independently transferred scalar estimates meet at the identical
filed far crop. The linear and bilinear return laws keep the two birth patterns. -/
theorem combine (h p : ℕ) (K : Set (YangMills.Points 2)) (compact : IsCompact K)
    (safe : K ⊆ YM.conf 2) {C B : ℝ} (hC : 0 < C) (hB : 0 < B)
    (independent : ∃ D : ℝ, 0 ≤ D ∧ ∃ e : ℕ, ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ s ≥ 0,
      exp s ≤ C*(gYM g.core r)^(-B) → ∀ farBorn : Bool, ∀ (y : Spacetime)
        (hy : (WithLp.toLp 2 ![0,y] : YangMills.Points 2) ∈ K) (u v : Sec g.core h),
        let f := r * exp s
        let L := AppointedCenteredReverse.transfer.{u} g hg periods strict h r f
        let x : Scale.Stage 2 := ⟨WithLp.toLp 2 ![0,y],safe hy⟩
        let F := Kseries (Z g hg) (Q.{u} g hg).MS h s
        let T := AppointedFixedBilinearCrop.secondField (Z g hg) (Q.{u} g hg).MS h s farBorn
        let psi := GroupS.ψ (Z g hg).criterion (Q.{u} g hg).MS (Teller.logNu 1) (-s)
        ‖AppointedReturnedBilinear.submitted.{u} g hg h p y (heat.{u} g hg periods strict f)
            (L u) (if farBorn then v else L v) -
          crop p (heat.{u} g hg periods strict r) ((AppointedBilinearCauchy.full (Z g hg) h x F T u v).subst psi)‖ ≤
          ‖chair g.core h u‖*‖chair g.core h v‖*(D*(gYM g.core r)^(p+1)*(1+s)^e)) :
    PairAtNearClock.{u} g hg periods strict h p K safe C B := by
  obtain ⟨D,hD,i,physical⟩ := AppointedCenteredPhysicalNames.pairedOnWindow.{u}
    g hg periods strict h p K compact safe hC hB
  obtain ⟨E,hE,j,returned⟩ := independent
  refine ⟨D+E,add_nonneg hD hE,i+j,?_⟩
  filter_upwards [physical,returned,positive_g (_root_.IssuedMaxwell.ElectedPrescription.simple g hg)] with r phys form hr
  intro s hs window u v phase o y hy
  let f := r * exp s
  let L := AppointedCenteredReverse.transfer.{u} g hg periods strict h r f
  let x : Scale.Stage 2 := ⟨WithLp.toLp 2 ![0,y 0],safe hy⟩
  let F := Kseries (Z g hg) (Q.{u} g hg).MS h s
  let psi := GroupS.ψ (Z g hg).criterion (Q.{u} g hg).MS (Teller.logNu 1) (-s)
  let t := heat.{u} g hg periods strict r
  let tf := heat.{u} g hg periods strict f
  have priced := phys s hs window u v phase o y hy
  have allNear := form s hs window false (y 0) hy u v
  have mixed := form s hs window true (y 0) hy u v
  change ‖AppointedReturnedBilinear.submitted.{u} g hg h p (y 0) tf (L u) (L v) -
    crop p t ((AppointedBilinearCauchy.full (Z g hg) h x F F u v).subst psi)‖ ≤ _ at allNear
  change ‖AppointedReturnedBilinear.submitted.{u} g hg h p (y 0) tf (L u) v -
    crop p t ((AppointedBilinearCauchy.full (Z g hg) h x F 1 u v).subst psi)‖ ≤ _ at mixed
  have atFar (b : Sec g.core h) : crop p tf (AppointedCenteredRows.series g hg h (L u) b (y 0)) =
      AppointedReturnedBilinear.submitted.{u} g hg h p (y 0) tf (L u) b :=
    AppointedCenteredRows.centeredCrop.{u} g hg h p (L u) b (y 0) tf (safe hy)
  rw [←atFar (L v),←AppointedTwoClocks.twice (Z g hg) (Q.{u} g hg).MS (Q.{u} g hg).matching h x s u v] at allNear
  rw [←atFar v,←AppointedTwoClocks.once (Z g hg) (Q.{u} g hg).MS (Q.{u} g hg).matching h x s u v] at mixed
  have mass := mul_nonneg (norm_nonneg (chair g.core h u)) (norm_nonneg (chair g.core h v))
  have growth := pow_nonneg hr.le (p+1)
  have width : 1 ≤ 1+s := le_add_of_nonneg_right hs
  exact ⟨join hD hE mass growth width priced.1 allNear, join hD hE mass growth width priced.2 mixed⟩

end YM.FVA2.GradedFar.AppointedCenteredPhysicalReturn

