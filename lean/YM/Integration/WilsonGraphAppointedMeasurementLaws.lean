import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.SignedAxes
import YangMills.WilsonProof.NativeSupport.WardBridge
import YM.Integration.WilsonPositionSeparatedProfileUnitFrame
import YangMills.WilsonProof.NativeSupport.IssuedBank.WilsonSlope
import YM.Integration.WilsonGraphAppointedPublicMeasurement

noncomputable section

namespace YM.Answer.ContinuumLimit.ElectedMeasurement

open Function Filter Set Asymptotics PowerSeries
open Lattice RG MeasureTheory Wilson Extraction Climb Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FullVolume Spec Table
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Fleet PhysMS PhysMS.Frame Next.UVStress OPE OPE.Orbits
open FVA2 FVA2.Register FVA2.Scale FVA2.Scale.Level
open SignedWilsonExpansion SignedWilsonExpansion.Belle SignedWilsonExpansion.Belle.Path SignedWilsonExpansion.Museum SignedWilsonExpansion.Kane
open SignedWilsonExpansion.Kane.Tilted SignedWilsonExpansion.Camera
open Integration.Election Integration.Election.Frames
open Order Spin SignedWilsonExpansion.StageG XSpace.Cirrus Entree Future
open Belfry Belle Dancer Belfry.ScaleFits Belfry.Classroom Scale Level GroupS
open Answer.ContinuumLimit Answer.ContinuumLimit.Vision
open Integration.GradedFar Integration.GradedFar.Tariff
open _root_.IssuedBridge
open scoped Topology BigOperators Classical ContDiff

open FVA2.GradedFar FVA2.Dframe
universe u
variable {g : YangMills.GaugeGroup} {H : g.core.Simple} {ε : ℝ}
variable {e : Axis} {O : OrderS g.core} {E : Construction.{u} H ε e O}
variable {ξ : Extraction.Order}


theorem adjusted (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) (d : ℕ) :
    ∀ᶠ r in trail, 0 < clock V Z r ∧
      ∀ v : (YangMills.maxwellReference g).sector d, frame V Z r d v =
        V.Pre Z r d ((Maxwell.Free.fields E.paths.family.labels d).symm
          (stand (Integration.WilsonPositionHomogeneousNear.field Z d (clock V Z r)) v)) := by
  filter_upwards [positive V Z Q, Integration.WilsonPositionHomogeneousFrame.fitted
    V.pupil.last V.pupil.J Z V.pupil.VFrame.2 V.pupil.VFrame.1 H d] with r hr fit
  refine ⟨hr, ?_⟩
  intro v
  change V.Pre Z r d (Integration.WilsonPositionHomogeneousFrame.change
    V.pupil.last V.pupil.J Z d r ((Maxwell.Free.fields E.paths.family.labels d).symm v)) = _
  rw [Integration.WilsonPositionHomogeneousFrame.change, dif_pos fit]
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.ofBijective_apply]
  rfl

theorem positiveRepresentative (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) (d : ℕ) :
    ∀ᶠ r in trail, ∀ v : (YangMills.maxwellReference g).sector d,
      frame V Z r d v = V.Pre Z r d ((Maxwell.Free.fields E.paths.family.labels d).symm
        (stand (Integration.WilsonPositionHomogeneousRealization.correction Z d (clock V Z r)) v)) := by
  filter_upwards [adjusted V Z Q d] with r hr
  simpa only [Integration.WilsonPositionHomogeneousNear.field, if_pos hr.1] using hr.2

theorem normalized (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) :
    Tendsto (fun r => clock V Z r * Real.sqrt (g.core.slopeConstant * Real.log r⁻¹))
      trail (𝓝 1) := by
  have positiveSlope : 0 < g.core.slopeConstant := YM.Gauge.slopeConstant_pos H
  have rate := (V.certificate Q).calendar.clock.running
  have constant : Tendsto (fun _ : ℝ => g.core.slopeConstant) trail (𝓝 g.core.slopeConstant) :=
    tendsto_const_nhds
  have scaled : Tendsto (fun r => g.core.slopeConstant * (Real.log r⁻¹ * (clock V Z r)^2))
      trail (𝓝 1) := by
    simpa only [clock, Vision.T, YM.Trace.Pilot.LogV, mul_inv_cancel₀ positiveSlope.ne'] using constant.mul rate
  have root := scaled.sqrt
  rw [Real.sqrt_one] at root
  apply root.congr'
  filter_upwards [positive V Z Q] with r hr
  rw [show g.core.slopeConstant * (Real.log r⁻¹ * (clock V Z r)^2) =
    (clock V Z r)^2 * (g.core.slopeConstant * Real.log r⁻¹) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hr.le]

theorem normalizedAtPublicBeta (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true)
    (normalization : 2 * YangMills.Matching.oneLoopBeta (YangMills.maxwellReference g) =
      g.core.slopeConstant) :
    Tendsto (fun r => clock V Z r *
      Real.sqrt (2 * YangMills.Matching.oneLoopBeta (YangMills.maxwellReference g) * Real.log r⁻¹))
      trail (𝓝 1) := by
  simpa only [normalization] using normalized V Z Q

theorem publicOneLoopSlope (hg : g.IsSimple) :
    2 * YangMills.Matching.oneLoopBeta (YangMills.maxwellReference g) = g.core.slopeConstant := by
  exact _root_.IssuedBank.WilsonSlope.original (YangMills.maxwellReference g) hg

theorem oneLoop (hg : g.IsSimple) (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) :
    Tendsto (fun r => clock V Z r *
      Real.sqrt (2 * YangMills.Matching.oneLoopBeta (YangMills.maxwellReference g) * Real.log r⁻¹))
      trail (𝓝 1) :=
  normalizedAtPublicBeta V Z Q (publicOneLoopSlope hg)

theorem pinIncluded (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    {d h : ℕ} (within : d ≤ h) (p : (YangMills.maxwellReference g).sector d) :
    ∀ᶠ r in trail, (YangMills.hierarchy V.pupil.last V.pupil.P).toLabel h
        (frame V Z r h (XSpace.Normalize.up within p)) =
      (YangMills.hierarchy V.pupil.last V.pupil.P).toLabel d (frame V Z r d p) := by
  filter_upwards [included V Z Q within] with r raised
  rw [raised p]
  exact V.pupil.last.sector.derivatives.stays (spectate V.pupil.last none).laws.toSymmetric
    (spectate_ready V.pupil.last none) within (frame V Z r d p)

theorem nested (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (d e : ℕ) (p : (YangMills.maxwellReference g).sector d)
    (q : (YangMills.maxwellReference g).sector e) (same : p.val = q.val) :
    ∀ᶠ r in trail, (YangMills.hierarchy V.pupil.last V.pupil.P).toLabel d (frame V Z r d p) =
      (YangMills.hierarchy V.pupil.last V.pupil.P).toLabel e (frame V Z r e q) := by
  rcases le_total d e with h | h
  · have qeq : XSpace.Normalize.up h p = q := Subtype.ext same
    filter_upwards [pinIncluded V Z Q h p] with r priced
    rw [← qeq]
    exact priced.symm
  · have peq : XSpace.Normalize.up h q = p := Subtype.ext same.symm
    filter_upwards [pinIncluded V Z Q h q] with r priced
    rw [← peq]
    exact priced

def includeField (V : Vision E ξ) {j h : ℕ} (hj : j ≤ h) :
    (YangMills.hierarchy V.pupil.last V.pupil.P).Field j →ₗ[ℂ]
      (YangMills.hierarchy V.pupil.last V.pupil.P).Field h :=
  V.pupil.last.sector.derivatives.rise hj

theorem includeLabel (V : Vision E ξ) {j h : ℕ} (hj : j ≤ h)
    (v : (YangMills.hierarchy V.pupil.last V.pupil.P).Field j) :
    (YangMills.hierarchy V.pupil.last V.pupil.P).toLabel h (includeField V hj v) =
      (YangMills.hierarchy V.pupil.last V.pupil.P).toLabel j v :=
  V.pupil.last.sector.derivatives.stays (spectate V.pupil.last none).laws.toSymmetric
    (spectate_ready V.pupil.last none) hj v

theorem includeInsertion (V : Vision E ξ) {j h : ℕ} (hj : j ≤ h)
    (v : (YangMills.hierarchy V.pupil.last V.pupil.P).Field j)
    (phase : Option (YangMills.hierarchy V.pupil.last V.pupil.P).Character)
    (n : ℕ) (a : Fin n → (YangMills.hierarchy V.pupil.last V.pupil.P).Tag)
    (x : YangMills.Points (n+1)) (hx : x ∈ YangMills.WilsonFamily.separated (n+1)) :
    (YangMills.hierarchy V.pupil.last V.pupil.P).correlation phase
      (Fin.cons ⟨h, includeField V hj v⟩ a) x =
    (YangMills.hierarchy V.pupil.last V.pupil.P).correlation phase (Fin.cons ⟨j,v⟩ a) x :=
  (spectate_ready V.pupil.last phase).kernels hj v hx a

theorem multilinear (V : Vision E ξ)
    (phase : Option (YangMills.hierarchy V.pupil.last V.pupil.P).Character)
    (n : ℕ) (d : Fin n → ℕ) (x : YangMills.Points n) (_hx : x ∈ YangMills.WilsonFamily.separated n) :
    ∃ moment : MultilinearMap ℂ (fun i => (YangMills.hierarchy V.pupil.last V.pupil.P).Field (d i)) ℂ,
      ∀ v, (YangMills.hierarchy V.pupil.last V.pupil.P).correlation phase (fun i => ⟨d i, v i⟩) x = moment v :=
  ⟨V.pupil.S.classMoment (spectator V.pupil.last phase) d x, fun _ => rfl⟩




theorem unitFrame (V : Vision E ξ) (Z : WilsonPrescription g.core) (d : ℕ) :
    ∀ᶠ r in trail, frame V Z r d (leaf g.core d) = V.pupil.S.unit d :=
  Integration.WilsonPositionSeparatedProfileUnitFrame.funded
    V.pupil.last V.pupil.J Z V.pupil.VFrame.2 d

theorem spectatorUnit (V : Vision E ξ) (phase : Peers V) {n : ℕ} (d : ℕ)
    (a : Fin n → V.pupil.S.Tag) (x : Points (n+1)) (hx : x ∈ conf (n+1)) :
    V.pupil.S.useAt (spectator V.pupil.last phase) x
      (Fin.cons ⟨d,V.pupil.S.unit d⟩ a) =
    V.pupil.S.useAt (spectator V.pupil.last phase) (Points.tail x) a := by
  let S := V.pupil.S
  let T := spectator V.pupil.last phase
  let w : Fin n → E.paths.family.book.Token := fun i =>
    ⟨(a i).1,S.representative _ (a i).2⟩
  let u := Fin.cons (α := fun _ : Fin (n+1) => E.paths.family.book.Token)
    (E.paths.family.book.one d) w
  have he (i) : S.classTokens (w i) = a i := by
    change Sigma.mk (a i).1 (S.project _ (S.representative _ _)) = a i
    rw [S.rep]
  have head : Fin.cons (α := fun _ : Fin (n+1) => S.Tag) ⟨d,S.unit d⟩ a =
      S.classTokens ∘ u := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [u, Function.comp_apply, Fin.cons_zero]
      rfl
    · simp only [u, Function.comp_apply, Fin.cons_succ, he]
  have ht : Points.tail x ∈ conf n := by
    intro i j h
    exact Fin.succ_injective _ (hx (show x.ofLp i.succ = x.ofLp j.succ from h))
  have hb := (spectate V.pupil.last phase).laws
  have hr := spectate_respects V.pupil.last phase
  change S.useAt T x (Fin.cons ⟨d,S.unit d⟩ a) = S.useAt T (Points.tail x) a
  rw [head, S.at_project T hb.toSymmetric hr hx, hb.unital hx d w,
    show a = S.classTokens ∘ w from funext fun i => (he i).symm,
    S.at_project T hb.toSymmetric hr ht]

theorem unit (V : Vision E ξ) (Z : WilsonPrescription g.core) (d : ℕ)
    (p : (YangMills.maxwellReference g).sector d) (hp : p.val = 1) :
    ∀ᶠ r in trail,
      ∀ (phase : Option (YangMills.hierarchy V.pupil.last V.pupil.P).Character) (n : ℕ)
        (a : Fin n → (YangMills.hierarchy V.pupil.last V.pupil.P).Tag) (x : YangMills.Points (n+1)),
        x ∈ YangMills.WilsonFamily.separated _ →
        (YangMills.hierarchy V.pupil.last V.pupil.P).correlation phase (Fin.cons ⟨d,frame V Z r d p⟩ a) x =
          (YangMills.hierarchy V.pupil.last V.pupil.P).correlation phase a (WithLp.toLp 2 (fun i => x.ofLp i.succ)) := by
  have same : p = leaf g.core d := Subtype.ext hp
  subst p
  filter_upwards [unitFrame V Z d] with r hr
  intro phase n a x hx
  change V.pupil.S.useAt (spectator V.pupil.last phase) x
      (Fin.cons ⟨d,frame V Z r d (leaf g.core d)⟩ a) =
    V.pupil.S.useAt (spectator V.pupil.last phase) (Points.tail x) a
  rw [hr]
  exact spectatorUnit V phase d a x hx


def AxisAppointment (V : Vision E ξ) (Z : WilsonPrescription g.core) : Prop :=
  ∃ W : (YangMills.hierarchy V.pupil.last V.pupil.P).StressWardLaws, ∀ d,
    ∀ᶠ s : ℝ in 𝓝[>] 0,
      ∀ (σ : Equiv.Perm YangMills.Axis) (sign : YangMills.Axis → ℝ)
        (U : YangMills.Spacetime ≃ₗᵢ[ℝ] YangMills.Spacetime) (R : YangMills.Ward.Rotation),
        (∀ a, sign a = 1 ∨ sign a = -1) →
        (∀ a, U (EuclideanSpace.single a 1) = sign a • EuclideanSpace.single (σ a) 1) →
        (∀ x, Matrix.toEuclideanLin R.val x = U x) →
        ∀ p q : (YangMills.maxwellReference g).sector d,
          YangMills.Matching.RelatedByAxes (YangMills.maxwellReference g) σ sign U p.val q.val →
          W.act d R (frame V Z s d p) = frame V Z s d q

def ofAxes (hg : g.IsSimple) (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) (axes : AxisAppointment V Z) :
    YangMills.Matching.CorrelationOnly.Measurement (YangMills.maxwellReference g)
      (YangMills.hierarchy V.pupil.last V.pupil.P) where
  clock := clock V Z
  positive := positive V Z Q
  oneLoop := oneLoop hg V Z Q
  frame := frame V Z
  nested := nested V Z Q
  frameAxes := axes
  unit := unit V Z
  includeField := includeField V
  includeLabel := includeLabel V
  includeInsertion := includeInsertion V
  multilinear := multilinear V

theorem clockOfAxes (hg : g.IsSimple) (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) (axes : AxisAppointment V Z) :
    (ofAxes hg V Z Q axes).clock = clock V Z := rfl

theorem frameOfAxes (hg : g.IsSimple) (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) (axes : AxisAppointment V Z) :
    (ofAxes hg V Z Q axes).frame = frame V Z := rfl

open YM.Maxwell.Free

theorem signedCoordinates (σ : Equiv.Perm YangMills.Axis) (sign : YangMills.Axis → ℝ)
    (U : YangMills.Spacetime ≃ₗᵢ[ℝ] YangMills.Spacetime) (R : YangMills.Ward.Rotation)
    (hs : ∀ a, sign a = 1 ∨ sign a = -1)
    (hu : ∀ a, U (EuclideanSpace.single a 1) = sign a • EuclideanSpace.single (σ a) 1)
    (hr : ∀ x, Matrix.toEuclideanLin R.val x = U x) :
    ∃ k : YM.Signed, k.perm = σ ∧ YM.Maxwell.Free.tilt k = sign ∧
      k.ortho = R ∧ YM.Ortho.motion k.ortho = U := by
  let k : YM.Signed := ⟨σ, fun a => decide (sign a = -1)⟩
  have sk : YM.Maxwell.Free.tilt k = sign := by
    funext a
    rcases hs a with h | h <;> simp [YM.Maxwell.Free.tilt, k, h] ; norm_num
  have kr : k.ortho = R := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    rw [← YM.M4.move_basis k.ortho.val i j, ← YM.M4.move_basis R.val i j]
    apply congrArg (fun y : YM.E4 => y i)
    have e : YM.Ortho.move k.ortho (YM.basis j) = sign j • YM.basis (σ j) := by
      simpa only [sk] using YM.Maxwell.Free.heads k j
    exact e.trans ((hu j).symm.trans (hr (YM.basis j)).symm)
  refine ⟨k, rfl, sk, kr, ?_⟩
  apply LinearIsometryEquiv.ext
  intro x
  rw [kr]
  exact hr x

theorem signedFrame (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) : AxisAppointment V Z := by
  refine ⟨YangMills.publicWards V.pupil.last V.pupil.P, ?_⟩
  intro d
  filter_upwards [((V.certificate Q).spin d).2] with s hs
  intro σ sign U R hsign hu hr a b hab
  obtain ⟨k, hp, hk, hR, hU⟩ := signedCoordinates σ sign U R hsign hu hr
  have rel : YangMills.Matching.RelatedByAxes (_root_.IssuedMaxwell.Reference.issued g)
      k.perm (YM.Maxwell.Free.tilt k) (YM.Ortho.motion k.ortho) a.val b.val := by
    rw [hp, hk, hU]
    exact hab
  have fields := (_root_.IssuedMaxwell.SignedAxes.original k a b).mp rel
  rw [← hR, fields]
  exact (V.pupil.last.phase.transport.spots.signed d k (frame V Z s d a)).trans
    (hs.2.2 k a).symm

def publicMeasurement (hg : g.IsSimple) (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) :
    YangMills.Matching.CorrelationOnly.Measurement (YangMills.maxwellReference g)
      (YangMills.hierarchy V.pupil.last V.pupil.P) :=
  ofAxes hg V Z Q (signedFrame V Z Q)

theorem publicClock (hg : g.IsSimple) (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) : (publicMeasurement hg V Z Q).clock = V.T Z := rfl

theorem publicFrame (hg : g.IsSimple) (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) : (publicMeasurement hg V Z Q).frame = frame V Z := rfl

theorem publicInputs (hg : g.IsSimple) (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) (s : ℝ) {n : ℕ}
    (d : Fin n → ℕ) (v : (i : Fin n) → (YangMills.maxwellReference g).sector (d i)) :
    (publicMeasurement hg V Z Q).inputs s (publicLetters d v) = inputs V Z s d v := rfl

end YM.Answer.ContinuumLimit.ElectedMeasurement




