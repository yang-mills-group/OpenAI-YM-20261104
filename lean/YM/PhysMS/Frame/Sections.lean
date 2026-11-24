import YM.PhysMS.Frame.Cost
import YM.TraceExtension.Atlas.Purse

/-! # Symmetry-compatible retraction on the *free* engineering grades

Use precisely the action used in Trace. It agrees with the action in the engineering
dilation routine (on the nose as operations on fields). -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysMS.Frame
open Function Set Filter Table Spec Climb Extra.FD Maxwell RG12.Roof Trace.Pilot
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (h:G.Simple) (F:Final C f S)
private lemma address_writes (C : Family G) (d : ℕ) : Free.address C.labels d = writes C.labels d := by
  apply LinearMap.ext; intro x; obtain ⟨v,rfl⟩:= (Bel C.book).onto d x
  rw [writes_project]; rfl

lemma ride_actual (C : Family G) (d : ℕ) (s : Ortho) (x : (Bel C.book).Field d) :
    rideO C.labels s d x = (turns C).act d s x := by
  apply Free.address_inj C.labels d
  let a := C.labels
  change Free.address a _ (ride C.labels s d x) = Free.address a _ (Free.tensorT a d s x)
  rw [Free.address_rot, address_writes C d, ride_at]
  obtain ⟨b,hb⟩:= Free.address_in C.labels d x
  rw [address_writes C d] at hb; rw [← hb, ← Free.pulls_label, ← observe_rot]

lemma corner_rotation (d : ℕ)(x:(Bel C.book).Field d)(hx:x∈Peak C.labels d)(s:Ortho):
    (turns C).act d s x∈Peak C.labels d := by
    change Pert.Scale.gear _ d 2 x - ((2:ℂ)^d) • x = 0 at hx
    rw [← ride_actual C]; change Pert.Scale.gear _ d 2 _ - ((2:ℂ)^d) • _= 0
    rw [← Pert.Scale.gear_spin,sub_eq_zero.mp hx,map_smul, LinearMap.id_apply, sub_self]

lemma corner_real (H:(Bel C.book).Hierarchy) (d : ℕ)(x:(Bel C.book).Field d)(hx:x∈Peak C.labels d):
    (Bel C.book).conj H.spin d x∈Peak C.labels d := by
    change Pert.Scale.gear _ d 2 x - ((2:ℂ)^d) • x = 0 at hx
    change Pert.Scale.gear _ d 2 (_root_.YM.Table.conj (Bel C.book) _ _ x) - ((2:ℂ)^d) • _= 0
    rw [show Pert.Scale.gear _ _ _ _ = _ from (Pert.Scale.gear_conj C.labels x 2).symm,sub_eq_zero.mp hx, map_smulₛₗ, map_pow, map_ofNat,LinearMap.id_apply]; exact sub_self _

set_option quotPrecheck false
local notation "K" => Free.scheme C.labels
local notation "lift" d => (Free.scheme C.labels).rise (Nat.le_succ d)
local notation "D" d => (Bel C.book).Field d
lemma complemented (C : Family G) (d : ℕ) : IsCompl (LinearMap.range ((Free.scheme C.labels).rise (Nat.le_succ d))) (Peak C.labels (d+1)) := (together _ (recorded C.labels (d+1))).symm

def peelDown (C : Family G)(d : ℕ): (Bel C.book).Field (d+1) →ₗ[ℂ] (Bel C.book).Field d :=
    LinearMap.linearProjOfIsCompl (Peak C.labels (d+1)) ((Free.scheme C.labels).rise (Nat.le_succ d))
     ((Free.scheme C.labels).inject (table_sym C.labels) (Free.scheme_filters C.labels) (Nat.le_succ d)) (complemented C d)

lemma section_up (d : ℕ)(x:D d) : peelDown C d ((lift d) x)=x:= LinearMap.linearProjOfIsCompl_apply_left ..
lemma section_same (d : ℕ)(x : D (d+1))(hx:x∈Peak C.labels (d+1)) : peelDown C d x=0:= LinearMap.linearProjOfIsCompl_apply_right' _ _ _ _ x hx

lemma spread (d : ℕ)(v : D (d+1)):∃ (x : D d) (y:D (d+1)), y∈Peak C.labels (d+1) ∧ v=(lift d) x + y:= by
   obtain ⟨x,y,h,-⟩:= Submodule.existsUnique_add_of_isCompl (complemented C d) v
   obtain ⟨b,hb⟩:= x.property
   exact ⟨b,y.val,y.property, hb.symm ▸ h.symm⟩
include h in
lemma section_rotation (d : ℕ)(x:D (d+1))(s: Ortho):peelDown C d ((turns C).act _ s x)=(turns C).act _ s (peelDown C d x) := by
    obtain ⟨p,q,hq,rfl⟩:=spread d x; have hk : Rotation.Laws (turns C) (K) (Maxwell.Free.hierarchy C.labels).spin := baseRights (C:=C) (H:=Free.hierarchy C.labels) h -- annotation?
    rw [map_add, hk.filtered, map_add,map_add,section_up,section_up,section_same d q hq,
      section_same d _ (corner_rotation _ _ hq s),add_zero,add_zero]
lemma section_real (H:(Bel C.book).Hierarchy) (d : ℕ)(x:D (d+1)):
    peelDown C d ((Bel C.book).conj H.spin _ x)=(Bel C.book).conj H.spin _ (peelDown C d x) := by
    obtain ⟨p,q,hq,rfl⟩:=spread d x
    rw [map_add, show (Bel C.book).conj H.spin _ ((lift d) p) = _ from (Free.phase_orientation C.labels).realInc (Nat.le_succ d) p, map_add,map_add,section_up,section_up,section_same d q hq, section_same d _ (corner_real H _ _ hq),add_zero,add_zero]
end YM.PhysMS.Frame
