import YangMills.WilsonProof.NativeSupport.Commissioned122.Scoped.YM.GradedFar.Fonds.Empty
import YangMills.WilsonProof.NativeSupport.Commissioned122.Scoped.YM.GradedFar.Toward.Contract
import YangMills.WilsonProof.NativeSupport.Commissioned122.Scoped.YM.GradedFar.Consistency
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedOrdinaryPacket
import YM.Integration.WilsonGraphPaperCorrelations

noncomputable section
namespace YM.FVA2.GradedFar.AppointedPublicNullary
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
open Function Filter Set MeasureTheory
open Register Scale Dframe OPE OPE.Orbits Trace.Pilot Integration
open O O.Enh O.Score XSpace XSpace.Normalize Compare
open YM.Answer.ContinuumLimit
open scoped Topology Classical BigOperators ContDiff

universe u
variable (g : YangMills.GaugeGroup) (hg : g.IsSimple) (dates : ℕ → ℕ) (strictDates : StrictMono dates)
variable (d : Fin 0 → ℕ) (h : ℕ)

theorem physical : ∀ᶠ r in trail, ∀ x : Points 0, ∀ o : E4, ∀ v : Appointed122Fields g.core d,
    cW (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonPositionHomogeneousFrame.homogeneous (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) r o x v (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.P h = leaf g.core h :=
  Fonds.vacant (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.P h d (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)).pupil.VFrame.2
    (M:=0) (δ:=1) zero_lt_one le_rfl

theorem prescribed (p : ℕ) (z : ℂ) (v : Appointed122Fields g.core d) (x : Points 0) :
    MScoefficient (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (Teller.logNu 1) (WilsonGraphPaperPublication.perspective.{u} g hg).MS x h p z v = leaf g.core h :=
  (exact_MS (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (Teller.logNu 1) (WilsonGraphPaperPublication.perspective.{u} g hg).MS (WilsonGraphPaperPublication.perspective.{u} g hg).matching x v h p z).trans
    (vector_empty (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg).matching x v h p z)

theorem measured : ∀ᶠ r in trail, ∀ x : Points 0, ∀ o : E4, ∀ v : Appointed122Fields g.core d,
    (AppointedOrdinaryPacket.measurement hg (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg)).wilsonOPE r h (fun i : Fin 0 => ⟨d i,v i⟩) o x = leaf g.core h := by
  filter_upwards [physical.{u} g hg dates strictDates d h] with r paid
  intro x o v
  exact (AppointedOrdinaryPacket.emptyPacket hg (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg) h d v r o x).trans (paid x o v)

theorem functions (p : ℕ) : ∀ᶠ r in trail, ∀ (o : E4) (v : Appointed122Fields g.core d),
    ∀ out : Sec g.core h →ₗ[ℂ] ℂ,
      (fun x : Points 0 => out ((AppointedOrdinaryPacket.measurement hg (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg)).wilsonOPE r h (fun i : Fin 0 => ⟨d i,v i⟩) o x)) = (fun _ => out (leaf g.core h)) ∧
      (fun x : Points 0 => out (MScoefficient (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (Teller.logNu 1) (WilsonGraphPaperPublication.perspective.{u} g hg).MS x h p ((AppointedOrdinaryPacket.measurement hg (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg)).clock r) v)) = (fun _ => out (leaf g.core h)) := by
  filter_upwards [measured.{u} g hg dates strictDates d h] with r paid
  intro o v out
  exact ⟨funext fun x => congrArg out (paid x o v),
    funext fun x => congrArg out (prescribed.{u} g hg d h p _ v x)⟩

theorem allOrders (p : ℕ) : ∀ᶠ r in trail, ∀ (o : E4) (v : Appointed122Fields g.core d),
    ∀ out : Sec g.core h →ₗ[ℂ] ℂ, ∀ k : ℕ, ∀ x : Points 0,
      ContDiffAt ℝ k (fun x : Points 0 => out ((AppointedOrdinaryPacket.measurement hg (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg)).wilsonOPE r h (fun i : Fin 0 => ⟨d i,v i⟩) o x)) x ∧
      ContDiffAt ℝ k (fun x : Points 0 => out (MScoefficient (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (Teller.logNu 1) (WilsonGraphPaperPublication.perspective.{u} g hg).MS x h p ((AppointedOrdinaryPacket.measurement hg (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg)).clock r) v)) x ∧
      iteratedFDeriv ℝ k (fun x : Points 0 => out ((AppointedOrdinaryPacket.measurement hg (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg)).wilsonOPE r h (fun i : Fin 0 => ⟨d i,v i⟩) o x)) x -
        iteratedFDeriv ℝ k (fun x : Points 0 => out (MScoefficient (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (Teller.logNu 1) (WilsonGraphPaperPublication.perspective.{u} g hg).MS x h p ((AppointedOrdinaryPacket.measurement hg (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg)).clock r) v)) x = 0 := by
  filter_upwards [functions.{u} g hg dates strictDates d h p] with r paid
  intro o v out k x
  obtain ⟨a,b⟩ := paid o v out
  rw [a,b,sub_self]
  exact ⟨contDiffAt_const,contDiffAt_const,rfl⟩

theorem underTest (p : ℕ) : ∀ᶠ r in trail, ∀ (o : E4) (v : Appointed122Fields g.core d),
    ∀ out : Sec g.core h →ₗ[ℂ] ℂ, ∀ (μ : Measure (Points 0)) (φ : Points 0 → ℂ),
      (∫ x, φ x * (out ((AppointedOrdinaryPacket.measurement hg (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg)).wilsonOPE r h (fun i : Fin 0 => ⟨d i,v i⟩) o x) - out (MScoefficient (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (Teller.logNu 1) (WilsonGraphPaperPublication.perspective.{u} g hg).MS x h p ((AppointedOrdinaryPacket.measurement hg (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg)).clock r) v)) ∂μ) = 0 := by
  filter_upwards [functions.{u} g hg dates strictDates d h p] with r paid
  intro o v out μ φ
  obtain ⟨a,b⟩ := paid o v out
  have zero (x : Points 0) : out ((AppointedOrdinaryPacket.measurement hg (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg)).wilsonOPE r h (fun i : Fin 0 => ⟨d i,v i⟩) o x) - out (MScoefficient (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (Teller.logNu 1) (WilsonGraphPaperPublication.perspective.{u} g hg).MS x h p ((AppointedOrdinaryPacket.measurement hg (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg)).clock r) v) = 0 :=
    sub_eq_zero.mpr ((congrFun a x).trans (congrFun b x).symm)
  simp only [zero,mul_zero,integral_zero]

end YM.FVA2.GradedFar.AppointedPublicNullary

