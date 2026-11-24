import YangMills.WilsonProof.NativeSupport.Commissioned259.Flash.Visit
/-! # FormalDemand including pre-adjustment kernel used at this window -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Flash
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score O.Enh Comparing Pose Original Matrix Quotes Sparks
open Flash259HorizonFork Facets Reg.Point
open scoped Topology ContDiff Classical BigOperators Matrix
variable {n m d :ℕ} {I:Type} {F:Filter I}{A:Set (Points n)}{B:Set (Points m)}
variable {W c δ a b:ℝ} {x:I→Points n}{y:I→Points m}{r T:I→ℝ} (R:Room W c δ A B)
local notation "late" => 𝓝[>] (0:ℝ)
variable {G:Gauge} {N : WilsonPrescription G} (ν:ℝ) {sim : G.Simple} {C : Family G}{f:Extraction.Order}{S:Table C.book}
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {σ: MS.Land.Prescription (Press.portDeck G)} {dial:Bool}
    (H:Main.Match N sim M σ dial)
    (h:Aim F G W a b r T) (hb:0<b) (hx:∀ᶠ i in F,x i∈A)(hy:∀ᶠ i in F,y i∈B)
variable (u:Tags G d (n+m))
local notation "V"=> Scale.Measure.outlook N.scheme N.criterion
local notation "P"=> Scale.Measure.start N.scheme N.criterion
local notation "Θ" => Scale.Measure.adjust N.scheme N.criterion
local notation "fK" => (fun i:I=> joins (x i) (y i) (T i))
include R h hx hy H ν
lemma trust (u:BasisSlots G (fun _:Fin (n+m)=>d)) : Tunes T F Pose.home (fun i=>storyV N (word u) (fK i)) := by
  let v : BasisSlots G (fun _:Fin n=>d) := u ∘ Fin.castAdd m; let w:BasisSlots G (fun _:Fin m=>d):=u ∘ Fin.natAdd n
  let P' := (H.separatedOPE ν).wilson
  have hc:= (whole_full P' R.compact_A R.near R.compact_B R.far (height R) R.event (GradedFar259.names v) (GradedFar259.names w) hx hy h.high)
  intro j; refine ((hc j).transport ( Comparing.fall (aspirant R h) _ )).congr ?_
  filter_upwards [permit R h hx hy] with i hi; rw [← read_basis (fun _=>le_rfl) (fun _=>le_rfl) _ _ P'.dimensions, PowerSeries.coeff_mk, Sparks.story_charge, fxt,dif_pos hi,bareRow_apply,kernel_on V hi]; congr 1; funext i; induction i using Fin.addCases <;> first| rw [ Fin.append_left ]; rfl| rw [Fin.append_right]; rfl
lemma PT_value (u:Tags G d (n+m)) : Tunes T F Pose.home (fun i=>storyV N u (fK i)) := by
  intro j; have e(q:BasisSlots G (fun _:Fin (n+m)=>d)):= trust R ν H h hx hy q j; simp_rw [ story_charge ] at e ⊢
  simp_rw [word_sigma u, smul_eq_mul ]; exact Fare.sum (aspirant R (by assumption)) fun i _=> Fare.cover ( Fare.constant _ ) (e i)
lemma pre_value (u:Tags G d (n+m)) : Tunes T F Pose.home (fun i=> Reg.Point.story (fxt (P d) (fK i)) u) := by
  have eq0 : actMark (Scale.mirror (Θ d)) (V d)=P d:= by rw [Scale.Measure.outlook, acts,(base_adjust N M H).turn', acts_h]
  intro j; have h' (b:Tags G d (n+m))(j) := PT_value R ν H h hx hy b j
  simp_rw [story_charge] at h'
  simp_rw [ ← eq0, fxt_m, Reg.Point.story, coeff_mk,seen ]; exact Fare.sum (aspirant R h) fun i _=> h' _ _
end YM.FVA2.GradedFar259.Flash
