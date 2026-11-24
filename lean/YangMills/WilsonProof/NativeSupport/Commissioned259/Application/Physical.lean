import YangMills.WilsonProof.NativeSupport.Commissioned259.Application.Primary
import YangMills.WilsonProof.NativeSupport.Commissioned259.ScaleCost.Pricing
import YangMills.WilsonProof.NativeSupport.Commissioned259.Flash.Focus
/-!
# Continuing the proof towards and through M.3: put together continuum G prices

Read these with their hypotheses (see INPUTS for relation to earlier (C5) in book). We have not
shown existence of these on the Run. We never take physical prices from the formal-to-formal MS
construction. G.1/G.6/G.9(i) progress, still not amended-estimator prices in THIS part of project.
QScale step implies the compact, growing and field-and-inverse bounds with the coherent H;
and also see README (e.g., for first polylog estimate from G.2 needed in Flash259HorizonFork).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalGradedFar
open Function Filter Set MeasureTheory Lattice Wilson RG Source Extraction Table Spec PhysicalNext.Repeat.Legato RG17 FullVolume OPE OPE.Orbits Climb Next.UVStress Trace.Pilot PhysMS
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open FVA2 FVA2.Register FVA2.GradedFar259 FVA2.Scale FVA2.O.Score FVA2.O.Enh FVA2.O.Canon Dframe
open MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land GradedFar259.Application Pose
open YM.Integration.WilsonPositionPrescribedFrame
open YM.Integration.WilsonPositionHomogeneousFrame
open scoped Topology BigOperators Classical
-- Original frame & horizon. Main.Match authentically; no relative choices. Even ν arbitrary.
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ→PhysMS.tower S) (N : WilsonPrescription G)
    (base : Leading F J) {sim : G.Simple} (ν : ℝ)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
local notation "late" => 𝓝[>] (0:ℝ)
local notation "W" => WilsonPositionPrescribedFrame.positioned F J N.store
local notation "B" => GroupS.gaugeN N.scheme N.criterion M ν
local notation "V" => Scale.Measure.outlook N.scheme N.criterion
local notation "t" => WilsonPositionHomogeneousFrame.reading F J N

open Asymptotics GradedFar259.ScaleCost GradedFar259.Original GradedFar259.Comparing
local notation "Z" => WilsonPositionHomogeneousFrame.homogeneous F J N
local notation "A₀" => WilsonPositionHomogeneousNear.field N
local notation "ψ" => GroupS.ψ N.criterion M ν
-- order-independent genuine arrival on both H and W. Earlier LOCAL inputs only.
open private leg from YM.Integration.WilsonPositionHomogeneousFrame
include H base
lemma real_frame (P: Receipt F J N) : GradedFar259.Quotes.Realized W Z N A₀ t := by
  constructor
  · have ht : Tendsto t late (𝓝 0):=(transition sim (OriginalGradedFar.calibration F J N base M H P)).trans_tendsto (g0_zero sim)
    intro d; filter_upwards [ht.eventually (WilsonPositionHomogeneousNear.invertible N d)] with r hr v
    exact congr_arg (W r d) (leg F J N hr v)
  · exact WilsonPositionHomogeneousNear.near N
  · intro d e; exact WilsonPositionHomogeneousNear.includes N (WilsonPositionHomogeneousCoefficients.purchased N H)
  intro d p; obtain ⟨A,hA,Q⟩:= WilsonPositionHomogeneousNear.expansion N d p
  refine IsBigO.of_bound A ?_; filter_upwards [self_mem_nhdsWithin (s:=Ioi (0:ℝ)), Q] with i hp hi
  rw [Real.norm_of_nonneg (pow_nonneg ( le_of_lt hp ) _ )]; exact hi
lemma true_h (P : Receipt F J N) : Leading F Z := GradedFar259.Quotes.Realized.leading F W Z N (WilsonPositionHomogeneousFrame.reading F J N) (true_w F J N base) (real_frame F J N base M H P) ((transition sim (OriginalGradedFar.calibration F J N base M H P)).trans_tendsto (g0_zero sim))
variable (Y: Shop F (WilsonPositionPrescribedFrame.positioned F J N.store) N)
    (hp : ∀ d:ℕ, GradedFar259.Quotes.Mixture F (WilsonPositionPrescribedFrame.positioned F J N.store) N d)
include Y
omit H base in
lemma eligible : Receipt F J N := ⟨6,2,le_rfl,le_rfl,Y 6 le_rfl 2 le_rfl (requests N 6)⟩
include hp
lemma G1 : StepCost G ψ B t (via Z) := GradedFar259.Quotes.G1_step F W Z N (true_w F J N base) (real_frame F J N base M H (eligible F J N Y)) ν M H Y (true_normal F J N base) hp
lemma G1compact (d p:ℕ)(X:Set ℝ)(hX:IsCompact X)(hm: 1≤p): ∃ C:ℝ,0<C ∧ ∀ᶠ r in late, ∀ η∈X,
    (let s := r*Real.exp (-η); let Ψ:= ψ η; let A:=via Z r s d; let X:=conversion B η d
     ‖(↑(t s):ℂ)-crop p (t r) Ψ‖ + stiffness (columns A-columns (GradedFar259.Quotes.accepts X p (t r))) ≤ C*g0 G r^(p+1)) :=
  ScaleCost.classic ((H.dilation ν).check) sim (transition sim (OriginalGradedFar.calibration F J N base M H (eligible F J N Y))) (checks Z) (reflexive Z) (G1 F J N base ν M H Y hp) hm X hX
local notation "g" => g0 G
lemma G1growing (d n:ℕ)(a b:ℝ)(hb:0<b) : (∀ᶠ p in atTop, ∃ C:ℝ,0<C ∧ ∀ᶠ r in late,
    ∀ T ≥ 1, T≤a*g r^(-b) → paired (via Z) B ψ t p d r T ≤ C*g r^n) ∧
    ∃ C:ℝ,0<C ∧ ∀ᶠ r in late,∀ T ≥ 1,T ≤ a*g r^(-b) →
      stiffness (actual (via Z) d r T) ≤ C*T^d ∧ stiffness (columns (via Z (r*T) r d)) ≤ C := by
  have hT:= transition sim (OriginalGradedFar.calibration F J N base M H (eligible F J N Y)); exact ⟨Original.price Z H hb hT (G1 F J N base ν M H Y hp) d n, weighing Z H hb hT (G1 F J N base ν M H Y hp) d⟩

variable (Q : Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (hQ:LogTrace F Q.port)
    (Paid: GradedFar259.Flash.Pays F (WilsonPositionPrescribedFrame.positioned F J N.store) N)
include hQ ν
-- exact G.6 inputs. No `Facilities` for this price; use locally at the real horizon
lemma G6 {I K:Type}[Fintype I][Fintype K]{d:I→ℕ}{e:K→ℕ}(L c δ:ℝ)(mn:0≤c)(dp:0<δ)(h:ℕ) :
    ∃ C :ℝ, 0<C ∧ ∃ k:ℕ, ∀ᶠ s:ℝ in late, ∀ r x y, OPE.Flash259HorizonFork.Ready r s c δ x y →
    ∀ o v w, ∀ u:(i:I)→Sec G (d i), Original.width L u → ∀ p:(i:K)→ Sec G (e i), Original.width L p →
      let D:= C*(g0 G r)⁻¹^k
      let Y s₂v:= Original.trueY F Z r s o s₂v x y u p; let M s₂v:= Original.trueD F Z r s o s₂v y p h; let X:= Original.trueC F Z Q r o x u h
      ‖Y v-M v X‖ ≤ D*(s+(r/s)^(h+1)) ∧
        ‖Y v‖+tallyZ (numbers X)+opCost (M v) ≤ D ∧
        ‖Y v-Y w‖+opCost (M v-M w) ≤ D*s :=
  Original.G6 F Z Q H (true_h F J N base M H (eligible F J N Y)) (fun n=> (G1 F J N base ν M H Y hp).fields n 0) hQ mn dp h
include Paid
lemma G9vals : supplies_round F Z V t := GradedFar259.Flash.provider F W Z N Q hQ (true_w F J N base) (true_normal F J N base) M H (real_frame F J N base M H (eligible F J N Y)) hp Y ν Paid
end YM.Integration.OriginalGradedFar
