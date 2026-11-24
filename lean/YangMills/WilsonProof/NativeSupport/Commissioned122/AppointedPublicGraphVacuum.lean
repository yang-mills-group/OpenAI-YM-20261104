import YangMills.WilsonProof.NativeSupport.Commissioned122.AppointedPublicNullary
import YangMills.WilsonProof.NativeSupport.Commissioned122.AppointedNullaryTariff

noncomputable section
namespace YM.FVA2.GradedFar.AppointedPublicGraphVacuum
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
open Function Set Filter MeasureTheory
open XSpace XSpace.Normalize Register Scale Dframe Trace.Pilot Integration
open O O.Score OPE OPE.Orbits Compare
open YangMills YangMills.MSbar
open YM.Answer.ContinuumLimit YangMills.Matching IssuedMaxwell IssuedMaxwell.Reports
open scoped BigOperators Classical Topology ContDiff

universe u
variable (g : YangMills.GaugeGroup) (hg : g.IsSimple)

private abbrev conversion := (WilsonGraphGroupPositionReference.external g hg).conversion.conversion

def graphCrop (a : Fin 0 → Ordinary.Label (B g)) (h p : ℕ) (z : ℂ) (x : Points 0) : Sec g.core h :=
  ∑ k ∈ Finset.range (p+1), z^k • (conversion g hg).ope (GraphCoefficients.issued g) h k a x

theorem filedValue (d : Fin 0 → ℕ) (v : Appointed122Fields g.core d) (a : Fin 0 → Ordinary.Label (B g))
    (h p : ℕ) (z : ℂ) (x : Points 0) :
    MScoefficient (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (Teller.logNu 1)
        (WilsonGraphPaperPublication.perspective.{u} g hg).MS x h p z v =
      graphCrop g hg a h p z x ∧ graphCrop g hg a h p z x = leaf g.core h := by
  have filed := AppointedNullaryTariff.wholeCrop.{u} g hg d v a h p x z
  exact ⟨filed, filed.symm.trans (AppointedPublicNullary.prescribed.{u} g hg d h p z v x)⟩

theorem filedCoefficients (d : Fin 0 → ℕ) (v : Appointed122Fields g.core d) (a : Fin 0 → Ordinary.Label (B g))
    (h k : ℕ) (x : Points 0) :
    (∀ p, MScoefficient (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (Teller.logNu 1)
      (WilsonGraphPaperPublication.perspective.{u} g hg).MS x h p 1 v = graphCrop g hg a h p 1 x) ∧
    (show Sec g.core h from (conversion g hg).ope (GraphCoefficients.issued g) h k a x) =
      if k = 0 then leaf g.core h else (0 : Sec g.core h) := by
  refine ⟨fun p => (filedValue.{u} g hg d v a h p 1 x).1, ?_⟩
  let row (i : ℕ) : Sec g.core h := (conversion g hg).ope (GraphCoefficients.issued g) h i a x
  have sums (p : ℕ) : (∑ i ∈ Finset.range (p+1), row i) = leaf g.core h := by
    simpa only [graphCrop, row, one_pow, one_smul] using (filedValue.{u} g hg d v a h p 1 x).2
  change row k = if k = 0 then leaf g.core h else (0 : Sec g.core h)
  cases k with
  | zero => simpa using sums 0
  | succ k =>
    have more := sums (k+1)
    rw [Finset.sum_range_succ, sums k] at more
    have eq : row (k+1) = (0 : Sec g.core h) :=
      add_left_cancel (more.trans (add_zero (leaf g.core h)).symm)
    simpa only [Nat.succ_ne_zero, if_false] using eq

variable (dates : ℕ → ℕ) (strictDates : StrictMono dates)
private abbrev chosen := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)
private abbrev heater (r : ℝ) : ℂ :=
  (chosen.{u} g hg dates strictDates).T (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) r
private abbrev W := AppointedOrdinaryPacket.measurement hg (chosen.{u} g hg dates strictDates)
  (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg)
variable (d : Fin 0 → ℕ) (h p : ℕ)

theorem onPick : ∀ᶠ r in trail, ∀ (o : E4) (v : Appointed122Fields g.core d) (a : Fin 0 → Ordinary.Label (B g))
    (out : Sec g.core h →ₗ[ℂ] ℂ),
    (fun x : Points 0 => out ((W.{u} g hg dates strictDates).wilsonOPE r h (fun i : Fin 0 => ⟨d i,v i⟩) o x)) =
      (fun _ => out (leaf g.core h)) ∧
    (fun x : Points 0 => out (graphCrop g hg a h p (heater.{u} g hg dates strictDates r) x)) =
      (fun _ => out (leaf g.core h)) := by
  filter_upwards [AppointedPublicNullary.measured.{u} g hg dates strictDates d h] with r paid
  intro o v a out
  exact ⟨funext fun x => congrArg out (paid x o v),
    funext fun x => congrArg out (filedValue.{u} g hg d v a h p (heater.{u} g hg dates strictDates r) x).2⟩

theorem allOrders : ∀ᶠ r in trail, ∀ (o : E4) (v : Appointed122Fields g.core d) (a : Fin 0 → Ordinary.Label (B g))
    (out : Sec g.core h →ₗ[ℂ] ℂ) (k : ℕ) (x : Points 0),
    let physical := fun y : Points 0 => out ((W.{u} g hg dates strictDates).wilsonOPE r h (fun i : Fin 0 => ⟨d i,v i⟩) o y)
    let formal := fun y : Points 0 => out (graphCrop g hg a h p (heater.{u} g hg dates strictDates r) y)
    ContDiffAt ℝ ∞ physical x ∧ ContDiffAt ℝ ∞ formal x ∧
      ‖iteratedFDeriv ℝ k physical x - iteratedFDeriv ℝ k formal x‖ ≤ 0 := by
  filter_upwards [onPick.{u} g hg dates strictDates d h p] with r paid
  intro o v a out k x
  obtain ⟨hw,hm⟩ := paid o v a out
  dsimp only
  rw [hw,hm,sub_self,norm_zero]
  exact ⟨contDiffAt_const,contDiffAt_const,le_rfl⟩

theorem underTest : ∀ᶠ r in trail, ∀ (o : E4) (v : Appointed122Fields g.core d) (a : Fin 0 → Ordinary.Label (B g))
    (out : Sec g.core h →ₗ[ℂ] ℂ) (μ : Measure (Points 0)) (φ : Points 0 → ℂ),
    (∫ x, φ x * (out ((W.{u} g hg dates strictDates).wilsonOPE r h (fun i : Fin 0 => ⟨d i,v i⟩) o x) -
      out (graphCrop g hg a h p (heater.{u} g hg dates strictDates r) x)) ∂μ) = 0 := by
  filter_upwards [onPick.{u} g hg dates strictDates d h p] with r paid
  intro o v a out μ φ
  obtain ⟨hw,hm⟩ := paid o v a out
  calc
    _ = ∫ _ : Points 0, (0 : ℂ) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [congrFun hw x,congrFun hm x,sub_self,mul_zero]
    _ = 0 := by simp

end YM.FVA2.GradedFar.AppointedPublicGraphVacuum

