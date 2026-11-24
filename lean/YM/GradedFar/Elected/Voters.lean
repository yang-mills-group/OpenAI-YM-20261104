import YM.GradedFar.Elected.Segments
import YM.Integration.WilsonPositionHomogeneousFrame
import YM.Integration.WilsonPositionPrescribedFrame
import YM.Integration.WilsonPositionHomogeneousComparison
import YM.SignedWilsonExpansion.Kane.Finale

/-!
# These are the book's actual field frames on this Run
-/
namespace YM.FVA2.GradedFar.Elected
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window
open OPE Orbits GradedFar.Physical Climb Next.UVStress Maxwell Maxwell.Free Trace.Pilot
open Integration Integration.WilsonPositionHomogeneousFrame
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m h k j t p : ℕ} (N : YM.FVA2.Register.WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
variable {R : PhysicalNext.Repeat.Legato.Run G} {f : Extraction.Order} {P : Table R.family.book}
    (U : Spec.Final R.family f P) (J:ℝ → PhysMS.tower P) (lead : PhysMS.Leading U J)

abbrev tallW := WilsonPositionPrescribedFrame.positioned U J N.store
abbrev tallH := WilsonPositionHomogeneousFrame.homogeneous U J N
abbrev Wframe := named (tallW N U J)
abbrev Hframe := named (tallH N U J)
local notation "θ"=>reading U J N
local notation "F"=> tallW N U J
local notation "W"=> Wframe N U J
local notation "T"=> Hframe N U J

abbrev held_W := WilsonPositionPrescribedScreen.hierarchy U F
abbrev Sframe (d:ℕ)(r:ℝ) := stand (WilsonPositionHomogeneousNear.field N d (reading U J N r))

lemma reading_equal : θ= Pose.kinetic N (familyPoint U W 6) := by
    funext v; apply congrArg (fun t:ℂ=> t.re / XSpace.Rose.cT N.criterion.cut G N.criterion.image)
    -- exact same tag profile, including all faces
    apply congrArg (XSpace.Rose.test N.criterion).applyTo; funext x; rfl

include lead
lemma holds (d:ℕ) : Held N (held_W N U J d) (familyPoint U W d) :=
    ⟨fun _ hr _ x => WilsonPositionPrescribedScreen.smooth U F x hr,
      fun _ hr n x v => WilsonPositionPrescribedScreen.actual U F d n v x hr,
      _root_.YM.Integration.WilsonPositionPrescribedFrame.original U J N.store lead d⟩
lemma oriented_W : oriented U (Wframe N U J) := by
    let X:=WilsonPositionPrescribedScreen.correction U J N.store
    refine growth_fields U (named J) W (legible U J lead) X (fun d=>?_) (fun d=> WilsonPositionPrescribedNested.fields U J lead N.store d)
    filter_upwards [(WilsonPositionPrescribedScreen.original U J lead N.store d).2] with r h u
    exact congrArg (J r d) (WilsonPositionPrescribedFrame.leg U J N.store h.2.1 u)

variable (P' : Physical.Ample N U (Wframe N U J))
include H P'
lemma got_time : Tendsto (fun i=> θ i/g i) τ (𝓝 1) :=
    (crown N M H U W (held_W N U J) θ (reading_equal N U J) P' (holds N U J lead)).1
lemma W_to_H (d:ℕ): ∀ᶠ r in τ,∀ x, T r d x=W r d (Sframe N U J d r x) := by
    have hp: Tendsto θ τ (𝓝 0):= Pose.tainted N M θ H (got_time N M H U J lead P')
    filter_upwards [hp.eventually (WilsonPositionHomogeneousNear.invertible N d)] with r he x
    apply congrArg (F r d)
    rw [WilsonPositionHomogeneousFrame.change,dif_pos he]
    change (Maxwell.Free.fields R.family.labels d).symm
      (Sframe N U J d r ((Maxwell.Free.fields R.family.labels d) ((Maxwell.Free.fields R.family.labels d).symm x)))= (Maxwell.Free.fields R.family.labels d).symm (Sframe N U J d r x)
    rw [LinearEquiv.apply_symm_apply]
lemma stocked : Bookshelf N U W T (Sframe N U J) (held_W N U J) θ ∧ oriented U T := by
    have hh:= W_to_H N M H U J lead P'
    have h':= oriented_W N U J lead
    have hz:= got_time N M H U J lead P'; have hp:= WilsonPositionHomogeneousCoefficients.purchased N H
    refine ⟨⟨holds N U J lead,permissible_ready N M H U W h',fun d=> charged_layer N M H W T (WilsonPositionHomogeneousNear.field N) θ hz d (hh d) (WilsonPositionHomogeneousNear.expansion N d), reading_equal N U J⟩, growth_fields U W T h' (fun d=> WilsonPositionHomogeneousNear.field N d ∘ θ) hh ?_⟩
    intro d; filter_upwards with r; exact fun x=> WilsonPositionHomogeneousNear.includes N hp (Nat.le_succ d) (θ r) x
end
end YM.FVA2.GradedFar.Elected
