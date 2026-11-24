import YM.GradedFar.Physical.Loom
import YM.PhysMS.Frame.Measured

/-!
# For the canonical position frame specialization on the Run
  Don't get a different prescription after taking the oriented witness. The
 `Match` input's gauge and frame charges work throughout.
-/
namespace YM.FVA2.GradedFar.Elected
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window
open OPE Orbits GradedFar.Physical Trace.Pilot Climb Next.UVStress Maxwell Maxwell.Free
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m h k j t p : ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (J:ℝ → PhysMS.tower P)

abbrev named : FramesH P := fun r d=> (Maxwell.Free.fields R.labels d).symm.trans (J r d)
-- alignment. Use Leading hypothesis of B data.
variable {d':ℕ}
private lemma cash_rise (u:Sec G n)(hr:n≤d') :
     (fields R.labels d').symm (up hr u)=(scheme R.labels).rise hr ((fields R.labels n).symm u) := by
   apply address_inj R.labels d'; rw [address_rise,address_eval,address_eval]
   rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]; rfl
private lemma cash_star (x:(Model R.labels).Field d') : fields R.labels d' ((Model R.labels).conj (spin_free R.labels) d' x)= reel d' (fields R.labels d' x):= Subtype.ext (address_star ..)
private lemma cash_face (s:Signed)(x:(Model R.labels).Field d') : fields R.labels d' ((Model R.labels).mirror (spin_free R.labels) d' s x)= ori s.ortho d' (fields R.labels d' x):= Subtype.ext (address_motion ..)
lemma legible (h : PhysMS.Leading U J) : oriented U (named J) where
   raises d e hd := by filter_upwards [h.raised hd] with r hr x; exact Eq.trans (congrArg (J r e) (cash_rise (R:=R) x hd)) (hr ((fields R.labels d).symm x))
   unit d := by
       filter_upwards [h.unit d] with r h
       have hp : leaf G d = fields R.labels d ((Model R.labels).unit d) := Subtype.ext ((unit_address R.labels d).symm)
       rw [hp]; exact (congrArg (J r d) ((fields R.labels d).symm_apply_apply _)).trans h
   real d := by
       filter_upwards [h.equivariant d] with r h u; obtain ⟨x,rfl⟩:= (fields R.labels d).surjective u
       rw [← cash_star]; change J r d ((fields R.labels d).symm _) = P.conj _ d (J r d ((fields R.labels d).symm _)); rw [LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply]; exact h.2 _
   signed d := by
       filter_upwards [h.equivariant d] with r h s u; obtain ⟨x,rfl⟩:= (fields R.labels d).surjective u
       rw [← cash_face]; change J r d ((fields R.labels d).symm _) = P.mirror _ d s (J r d ((fields R.labels d).symm _)); rw [LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply]; exact h.1 _ _
end
end YM.FVA2.GradedFar.Elected
