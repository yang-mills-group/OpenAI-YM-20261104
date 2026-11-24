import YM.Integration.WilsonGraphAppointedPositionFrame
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.AppointedPrescription
set_option autoImplicit false
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


theorem preSpectatorUnit (V : Vision E ξ) (phase : Peers V) {n : ℕ} (d : ℕ)
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

theorem preUnitAt (V : Vision E ξ) (Z : WilsonPrescription g.core)
    {lamp : Bool} (Q : Perspective H Z lamp) (d : ℕ) :
    ∀ᶠ r in trail, preFrame V Z r d (leaf g.core d) = V.pupil.S.unit d := by
  filter_upwards [((V.certificate Q).spin d).1] with r actual
  exact actual.1

theorem preUnital (V : Vision E ξ) (Z : WilsonPrescription g.core)
    {lamp : Bool} (Q : Perspective H Z lamp) :
    YangMills.MSbar.PositionUnital (YangMills.hierarchy V.pupil.last V.pupil.P)
      (preFrame V Z) := by
  intro d u hu
  have same : u = leaf g.core d := Subtype.ext hu
  subst u
  filter_upwards [preUnitAt V Z Q d] with r unitAt
  intro n a x hx
  change V.pupil.S.useAt (spectator V.pupil.last none) x
      (Fin.cons ⟨d,preFrame V Z r d (leaf g.core d)⟩ a) =
    V.pupil.S.useAt (spectator V.pupil.last none) (Points.tail x) a
  rw [unitAt]
  exact preSpectatorUnit V none d a x hx

theorem appointedTriangleCut (hg : g.IsSimple) :
    (_root_.IssuedMaxwell.ElectedPrescription.issued g hg).criterion.cut =
      (_root_.IssuedMaxwell.ElectedPrescription.prior g hg).val.triangle.cut :=
  (_root_.IssuedMaxwell.AppointedPrescription.original
    (_root_.IssuedMaxwell.ElectedPrescription.simple g hg)
    (_root_.IssuedMaxwell.ElectedPrescription.prior g hg).val
    (_root_.IssuedMaxwell.ElectedPrescription.prior g hg).property).2.2.2.1

theorem appointedTriangleProfile (hg : g.IsSimple) :
    ∀ x, (((_root_.IssuedMaxwell.ElectedPrescription.issued g hg).criterion.image x) : ℂ) =
      (_root_.IssuedMaxwell.ElectedPrescription.prior g hg).val.triangle.profile x :=
  (_root_.IssuedMaxwell.AppointedPrescription.original
    (_root_.IssuedMaxwell.ElectedPrescription.simple g hg)
    (_root_.IssuedMaxwell.ElectedPrescription.prior g hg).val
    (_root_.IssuedMaxwell.ElectedPrescription.prior g hg).property).2.2.2.2.1

theorem appointedTrianglePrice (hg : g.IsSimple) :
    cT (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) =
      (_root_.IssuedMaxwell.ElectedPrescription.prior g hg).val.triangle.cT :=
  (_root_.IssuedMaxwell.AppointedPrescription.original
    (_root_.IssuedMaxwell.ElectedPrescription.simple g hg)
    (_root_.IssuedMaxwell.ElectedPrescription.prior g hg).val
    (_root_.IssuedMaxwell.ElectedPrescription.prior g hg).property).2.2.2.2.2.1

theorem preClockAtSignal (V : Vision E ξ) (Z : WilsonPrescription g.core)
    {lamp : Bool} (Q : Perspective H Z lamp) (r : ℝ) :
    V.T Z r = (Signal V Z r).re / cT Z := by
  apply (eq_div_iff (ne_of_lt (V.certificate Q).c_neg)).2
  simpa only [mul_comm] using (V.certificate Q).c_paid r

theorem preClockAtFiledTriangle (hg : g.IsSimple) (V : Vision E ξ)
    {lamp : Bool}
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) lamp) (r : ℝ) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    V.T Z r = (Signal V Z r).re /
      (_root_.IssuedMaxwell.ElectedPrescription.prior g hg).val.triangle.cT := by
  simpa only [appointedTrianglePrice hg] using
    (preClockAtSignal V (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) Q r)

end YM.Answer.ContinuumLimit.ElectedMeasurement
