import YM.Integration.WilsonPublicForkSeats
import YM.OPE.Orbits.System

/-! Read the same measured compact packet in the original ordering of its
physical sources. The far source and all the intermediate grades survive reindexing. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkLabels
open Function Finset Set Filter Table Spec OPE OPE.Prescription OPE.Orbits OPE.Orbits.Reader OPE.Arboreal
open WilsonPublicForkGeometry WilsonPublicForkRooms
open scoped Classical Topology BigOperators
variable {I:Type} [Fintype I]
def index : ↥(near I)≃I:=nearSeat.symm

theorem slots (r t:ℝ)(x:I→E4)(z:E4):
    crop (WilsonPublicForkGeometry.position r t x z) (near I) = (fun i=>r • x i) ∘ index :=by
  funext j; obtain ⟨i,rfl⟩:=(nearSeat (I:=I)).surjective j
  change r • x i=r • x (nearSeat.symm (nearSeat i))
  rw [Equiv.symm_apply_apply]

variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {d:I→ℕ}
theorem grouped (h:ℕ)(x:I→E4)(v:Labels S d):
    Q.packet h (x ∘ index) (d:=d ∘ index) (fun i=>v (index i)) 0=Q.packet h x v 0:=by
  unfold Reader.packet
  exact Finset.sum_congr rfl (fun j _=>congr_arg _ (Q.fresh_perm j x 0 (d:=d) v index))

def defect (e h:ℕ)(x:I→E4)(v:Labels S d)(Y:S.Field h)(z:E4):S.Field e→ₗ[ℂ]ℂ:=
   upon S e z x v - upon S e z (sole 0) (sole Y:Labels S (fun _:Unit=>h))

theorem signed {e h:ℕ}(x:I→E4)(v:Labels S d)(z:E4)(w:S.Field e)
    (sep:Injective (beside x (sole z)))(ext:Injective (beside (sole (0:E4)) (sole z))):
    formula F Q (x ∘ index) 0 (d:=d ∘ index) (fun i=>v (index i)) (sole z)
      (sole w:Labels S (fun _:Unit=>e)) h none=defect e h x v (Q.packet h x v 0) z w:=by
  let b:Labels S (fun _:Unit=>e):=sole w
  let Y:=Q.packet h x v 0
  rw [formula,←packet_read F Q _ _ _ _ _ none h ext,grouped F Q]
  change whole S (x ∘ index) (d:=d ∘ index) (fun i=>v (index i)) (sole z) b-upon S h 0 (sole z) b Y=_
  have perm:whole S (x ∘ index) (d:=d ∘ index) (fun i=>v (index i)) (sole z) b=
      whole S x v (sole z) b:=whole_perm S (d:=d) index (Equiv.refl Unit) Q.continuum sep
  rw [perm]
  change _-whole S (sole 0) (sole Y:Labels S (fun _:Unit=>h)) (sole z) b=
    whole S (sole z) b x v-whole S (sole z) b (sole 0) (sole Y:Labels S (fun _:Unit=>h))
  rw [whole_flip v b x (sole z) Q.continuum sep,whole_flip (sole Y:Labels S (fun _:Unit=>h)) b (sole 0) (sole z) Q.continuum ext]

def packet (h:ℕ)(x:I→E4):MultilinearMap ℂ (fun i=>S.Field (d i)) (S.Field h):=
  ∑i:Fin (h+1),(F.sector.derivatives.rise (d:=i.val) (by omega)).compMultilinearMap (Q.fresh i.val x 0)
def forms (e h:ℕ)(x:I→E4)(z:E4)(w:S.Field e):MultilinearMap ℂ (fun i=>S.Field (d i)) ℂ:=
  let T:MultilinearMap ℂ (fun i=>S.Field (d i)) ℂ:=
    sectionLabels (d:=Sum.elim d (fun _:Unit=>e)) (sole w) (moment S (beside x (sole z)))
  T - (upon S h 0 (sole z) (sole w:Labels S (fun _:Unit=>e))).compMultilinearMap (packet F Q h x)

theorem actual {e h:ℕ}(x:I→E4)(v:Labels S d)(z:E4)(w:S.Field e)
    (sep:Injective (beside x (sole z)))(ext:Injective (beside (sole (0:E4)) (sole z))):
    forms F Q e h x z w v=defect e h x v (Q.packet h x v 0) z w:=by
  have pkt:packet F Q h x v=Q.packet h x v 0:=by
    rw [packet,Reader.packet,_root_.sum_apply];rfl
  unfold forms
  change sectionLabels (d:=Sum.elim d (fun _:Unit=>e)) (sole w) (moment S (beside x (sole z))) v -
     upon S h 0 (sole z) (sole w:Labels S (fun _:Unit=>e)) (packet F Q h x v)=_
  rw [sectionLabels_apply,pkt]
  let Y:=Q.packet h x v 0
  change whole S x v (sole z) (sole w:Labels S (fun _:Unit=>e))-
    whole S (sole 0) (sole Y:Labels S (fun _:Unit=>h)) (sole z) (sole w:Labels S (fun _:Unit=>e))=
    whole S (sole z) (sole w:Labels S (fun _:Unit=>e)) x v-
    whole S (sole z) (sole w:Labels S (fun _:Unit=>e)) (sole 0) (sole Y:Labels S (fun _:Unit=>h))
  rw [whole_flip v (sole w:Labels S (fun _:Unit=>e)) x (sole z) Q.continuum sep,
    whole_flip (sole Y:Labels S (fun _:Unit=>h)) (sole w:Labels S (fun _:Unit=>e)) (sole 0) (sole z) Q.continuum ext]

end YM.Integration.WilsonPublicForkLabels
