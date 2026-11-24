import YM.Integration.WilsonGraphCenteredFarPhysicalMass
import YM.Integration.WilsonGraphCenteredFarHeaterRate

set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar.AppointedCenteredPhysicalPrice

open Filter Real Growth Continuation
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open MS MS.Book MS.Land Scale Register O O.Enh O.Score Dframe
open YangMills YangMills.Matching YM.Answer.ContinuumLimit YM.Integration
open WilsonGraphPublishedShapeEstimate WilsonGraphPreElectedShapeEstimates
open WilsonGraphCenteredFarReplacement (atFar PairPrice)
open scoped Topology BigOperators Classical

universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)
private abbrev pick := WilsonGraphPaperPublication.publicPick.{u} g hg
  (ElectedPublication.order periods strict)
private abbrev scheme := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev hierarchy := YangMills.hierarchy (g := g) (pick.{u} g hg periods strict).pupil.last
  (pick.{u} g hg periods strict).pupil.P
private abbrev heater := ElectedMeasurement.clock (pick.{u} g hg periods strict) (scheme g hg)
private abbrev field := ElectedMeasurement.frame (pick.{u} g hg periods strict) (scheme g hg)

/-- The physical two-point reading at its actual birth radii and the cropped independent
centered pair expressed at the far radius. The origin and phase are the submitted ones. -/
def discrepancy (h q : ℕ) (r s f : ℝ) (a b center far : Sec g.core h)
    (phase : Option (hierarchy.{u} g hg periods strict).Character) (o y : Spacetime) : ℝ :=
  let x : YangMills.Points 2 := WithLp.toLp 2 ![0,y]
  ‖(hierarchy.{u} g hg periods strict).correlation phase
      ![⟨h,field.{u} g hg periods strict r h a⟩,⟨h,field.{u} g hg periods strict s h b⟩]
      (WithLp.toLp 2 fun i => o + f • x.ofLp i) -
    crop q (heater.{u} g hg periods strict f) (AppointedCenteredRows.series g hg h center far y)‖

set_option pp.universes true in
private theorem filed (h q : ℕ) (A r s f : ℝ) (a b center far : Sec g.core h)
    (phase : Option (hierarchy.{u} g hg periods strict).Character) (o y : Spacetime)
    (paid : AppointedCenteredRows.FiledPair.{u} g hg periods strict h q A r s f a b center far phase o y) :
    discrepancy.{u} g hg periods strict h q r s f a b center far phase o y ≤
      A * sectorMass (B := _root_.IssuedMaxwell.Reports.B g) center *
        sectorMass (B := _root_.IssuedMaxwell.Reports.B g) far * |heater.{u} g hg periods strict f|^(q+1) := by
  let x : YangMills.Points 2 := WithLp.toLp 2 ![0,y]
  let t := heater.{u} g hg periods strict f
  let Q := WilsonGraphPaperPublication.perspective.{u} g hg
  let conv := _root_.IssuedBridge.PostedAppointedConversion.filed (scheme g hg) Q.MS Q.matching (Teller.logNu 1)
  let polynomial := ∑ k : Fin (q+1), (t : ℂ)^k.val * WilsonGraphStandaloneCorrelation.converted
    conv k.val (publicLetters (fun _ : Fin 2 => h) ![center,far]) x
  let W := (hierarchy.{u} g hg periods strict).correlation phase
    ![⟨h,field.{u} g hg periods strict r h a⟩,⟨h,field.{u} g hg periods strict s h b⟩]
    (WithLp.toLp 2 fun i => o + f • x.ofLp i)
  have original : ‖W - polynomial‖ ≤
      (A * ∏ i : Fin 2, sectorMass (B := _root_.IssuedMaxwell.Reports.B g) (![center,far] i)) *
        |t|^(q+1) := paid.1
  have matchValue : crop q t (AppointedCenteredRows.series g hg h center far y) = polynomial := paid.2
  change ‖W - crop q t (AppointedCenteredRows.series g hg h center far y)‖ ≤ _
  rw [matchValue]
  simpa [Fin.prod_univ_two,mul_assoc] using original

private theorem price {A E F u v c d t x l : ℝ} (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hd : 0 ≤ d) (ht : 0 ≤ t)
    (left : c ≤ E * (2*u)) (right : d ≤ E * (2*v)) (clock : t ≤ F*x*l) :
    A*c*d*t ≤ (4*A*E^2*F) * (u*v) * x*l := by
  have product : A*c*d ≤ A*(E*(2*u))*(E*(2*v)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left left hA) right hd (by positivity)
  calc _ ≤ (A*(E*(2*u))*(E*(2*v)))*(F*x*l) := mul_le_mul product clock ht (by positivity)
       _ = _ := by ring

/-- A single compact payment on the actual pair gives both centered physical errors at
all admitted distances. The powers are evaluated at the near ruler and its log distance. -/
theorem onWindow (h q : ℕ) (K : Set (YangMills.Points 2)) (compact : IsCompact K)
    (separated : K ⊆ YM.conf 2) {C B : ℝ} (hC : 0 < C) (hB : 0 < B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ e : ℕ, ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ s ≥ 0,
      exp s ≤ C * (gYM g.core r)^(-B) →
      ∀ (a b : Sec g.core h) (phase : Option (hierarchy.{u} g hg periods strict).Character)
        (o y : Spacetime), (WithLp.toLp 2 ![0,y] : YangMills.Points 2) ∈ K →
        let f := r * exp s
        let la := atFar.{u} g hg periods strict h r f a
        let lb := atFar.{u} g hg periods strict h r f b
        let expense := D * (‖chair g.core h a‖ * ‖chair g.core h b‖) *
          (gYM g.core r)^(q+1) * (1+s)^e
        discrepancy.{u} g hg periods strict h q r r f a b la lb phase o y ≤ expense ∧
        discrepancy.{u} g hg periods strict h q r f f a b la b phase o y ≤ expense := by
  obtain ⟨A,hA,paid⟩ := AppointedCenteredWindowReadings.onBothRulers.{u}
    g hg periods strict h q q K compact separated hC hB
  obtain ⟨_,_,_,rows⟩ := paid.exists
  obtain ⟨E,hE,masses⟩ := AppointedCenteredPhysicalMass.onWindow.{u} g hg periods strict h hC hB
  obtain ⟨F,hF,e,heats⟩ := AppointedCenteredTransport.farHeaterPower.{u} g hg periods strict q hC hB
  refine ⟨4*A*E^2*F,by positivity,e,?_⟩
  filter_upwards [rows,masses,heats] with r actual fieldMass clock
  intro s hs admitted a b phase o y hy f la lb expense
  obtain ⟨both,once⟩ := (actual s hs admitted).1 a b phase o y hy
  have left := (fieldMass s hs admitted a).1
  have moved := (fieldMass s hs admitted b).1
  have fixed : sectorMass (B := _root_.IssuedMaxwell.Reports.B g) b ≤ E * (2 * ‖chair g.core h b‖) :=
    (fieldMass s hs admitted b).2.trans (mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (chair g.core h b)]) hE)
  have fee := (clock s hs admitted).1
  refine ⟨(filed.{u} g hg periods strict h q A r r f a b la lb phase o y both).trans ?_,
    (filed.{u} g hg periods strict h q A r f f a b la b phase o y once).trans ?_⟩
  · exact price hA hE (norm_nonneg _) (norm_nonneg _) (sectorMass_nonneg _) (pow_nonneg (abs_nonneg _) _) left moved fee
  · exact price hA hE (norm_nonneg _) (norm_nonneg _) (sectorMass_nonneg _) (pow_nonneg (abs_nonneg _) _) left fixed fee

end YM.FVA2.GradedFar.AppointedCenteredPhysicalPrice
