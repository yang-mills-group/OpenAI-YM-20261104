import YM.GradedFar.Elected.Remainder
import YM.GradedFar.Physical.Look
import YM.GradedFar.Physical.Elevated
import YM.GradedFar.Physical.Face
import YM.GradedFar.Logged.G7

/-!
# Application to the chosen field & packet horizons, progress beyond (M.2)
-/
namespace YM.FVA2.GradedFar.Elected
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window
open OPE Orbits GradedFar.Physical Climb Next.UVStress Trace.Pilot
open Integration Integration.WilsonPositionHomogeneousFrame
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m h k j t p : ℕ} (N : YM.FVA2.Register.WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
variable {R : PhysicalNext.Repeat.Legato.Run G} {f : Extraction.Order} {P : Table R.family.book}
    (U : Spec.Final R.family f P) (J:ℝ → PhysMS.tower P) (lead : PhysMS.Leading U J)
local notation "θ"=> reading U J N
local notation "W"=> Wframe N U J
local notation "T"=> Hframe N U J
-- credit synopsis. leave Grids & Ample exposed on actual election.
variable (Q' : Ample N U (Wframe N U J))
include H lead Q'
lemma G1_lane : Earned N M U W T θ :=
    Physical.booked N M H U (Wframe N U J) (Hframe N U J) (Sframe N U J) (held_W N U J) θ Q' (stocked N M H U J lead Q').1
/-- Also any compact interval (|s| ≤ v) as in G.1; doesn't require rebooking a new scale norm. -/
lemma G1_compact (v:ℝ)(p d:ℕ)(hp:1 ≤ p) : ∃ C:ℝ,0<C ∧ ∀ᶠ r in τ, ∀ s:ℝ,|s|≤v → ScaleBudget.money N M T θ p d r s ≤ C*g r^(p+1) := ScaleBudget.G1_other N M H U W T θ (G1_lane N M H U J lead Q') v p d hp
variable
    (Q : Reader U.sector.derivatives U.sector.turns U.room.kernel.spin) (hq : LogTrace U Q.port)
    (prior: Round.Grid N U (Wframe N U J))
include hq
lemma G6 {d:Fin n→ℕ}{e:Fin m→ℕ} {X:Set (Points n)}{Y:Set (Points m)} (hX:IsCompact X)(hx:X⊆conf n)(hY:IsCompact Y)(hy:Y⊆Outside m) (h:ℕ)(L R':ℝ):
    ∀ᶠ k:ℝ in atTop,∃ D:ℝ,0<D ∧ ∀ C B:ℝ,0<C→ 0<B→ ∀ᶠ (w:Continuation.Window) in windows (upper G C B),
      ∀ o:View U,∀x∈X,∀y∈Y,∀(u:Inputs G d),Within L u →∀(v:Inputs G e),Within R' v →∀(a:Sec G h), Ball 1 a →
       Physical.Owed U Q T k D h w.len w.Coarse o x y u v a :=
    Physical.horizon_lease d e N M H U Q W T θ (G1_lane N M H U J lead Q') (stocked N M H U J lead Q'|>.2) hq hX hx hY hy h L R'
include prior
/-- All M.3-consuming values of the physical pieces here; (G.6) prior log estimates & (C.5)
 still hypotheses of the proof. -/
lemma G9_value : SourceCost N U T θ := Round.rounded_world N M H U W T _ _ θ Q (stocked N M H U J lead Q' |>.1) (G1_lane N M H U J lead Q') (stocked N M H U J lead Q' |>.2) hq (W_to_H N M H U J lead Q') prior
/-- Now spend them. -/
lemma continues : Towards N M U T θ Q := books_paid N M H U W T _ _ θ Q (stocked N M H U J lead Q'|>.1) (G1_lane N M H U J lead Q') (stocked N M H U J lead Q' |>.2) hq (W_to_H N M H U J lead Q') prior
open MeasureTheory
-- any joint tests at these costs on (M.3)
/-- M.3 including **joint test** in x,y, including even with o (center) varying over the test. Pair with finite vector-valued measures & fixed viewing phase. Applies also to point measures. Costs don't use separate weighted-leg vacancies in comparisons. Preserve x, y, Ty and the true Far fields in Y and each D including D c_W. Use with `Near` arity nonempty. Costs at c≤C use all windows in that band. Sufficient `∀T≥T0 (T0 sufficiently large for this profile)` as in source. Unpack via `Continuation.Window.windows_eventually`.
-/
lemma M3 (η c C L R':ℝ)(hη : η < 1) (hc:0<c)(hC:c≤C) {X:Set (Points n)}{Y:Set (Points m)}(hX:IsCompact X)(hx:X⊆ conf n)(hY:IsCompact Y)(hy:Y⊆ Outside m)(hn:0<n)(d:Fin n→ℕ)(e:Fin m→ℕ)(p h:ℕ) (I:Type)[TopologicalSpace I][CompactSpace I][MeasurableSpace I][OpensMeasurableSpace I] :
   ∀ᶠ B:ℝ in atTop, ∀ᶠ j:ℕ in atTop, Tolerates N M U T Q θ d e X Y p h j c C η B L R' ∧ ∃ D':ℝ,0<D' ∧ ∀ᶠ (w:Continuation.Window) in windows (band G c C B), ∀ (Q0:Tasks.Data U X Y I), ∀ u: Inputs G d, Within L u → ∀ v:Inputs G e, Within R' v →
       Tasks.joint N M U T Q θ Q0 h j p η w u v D' := by
    apply ((continues N M H U J lead Q' Q hq prior).advanced n m d e X Y hn hX hx hY hy p h L R' c C η hc hC hη).mono
    intro B h0; exact h0.mono (fun j hj=> ⟨hj,Tasks.retained N M H U T Q θ hX hx hY hy hj⟩)

end
end YM.FVA2.GradedFar.Elected

