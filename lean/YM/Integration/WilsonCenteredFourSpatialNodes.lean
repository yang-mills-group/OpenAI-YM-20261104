import YM.Integration.WilsonThermometerWeakPairSector
import YM.Integration.WilsonCenteredFourOutputMoving

/-! The two locations of the physical tree read both original near letters,
and the complete measured packet is subtracted before evaluating the far arm. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourSpatialNodes
open Function Finset Set Filter Table Spec OPE OPE.Orbits OPE.Orbits.Reader OPE.Arboreal
open WilsonThermometerWeakPairRooms PhysMS PhysicalNext.Repeat.Legato
open scoped Classical Topology
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

private def nearIndex : ↥near ≃ Fin 2 where
  toFun a:=if a.1=2 then 0 else 1
  invFun i:=if i=0 then ⟨2,by decide⟩ else ⟨3,by decide⟩
  left_inv:=by decide
  right_inv:=by decide

def lift {X:Type*} (v:Fin 2→X):↥near→X := v ∘ nearIndex

theorem slots (r t:ℝ)(x:Fin 2→E4)(z:E4):
    crop (WilsonThermometerWeakPairFork.position r t (x 0) (x 1) z) near = lift (fun i=>r • x i):=by
  funext ⟨i,seat⟩
  rcases (by simpa only [near,Finset.mem_insert,Finset.mem_singleton] using seat : i=2 ∨ i=3) with rfl|rfl <;> rfl

theorem grouped (m:ℕ)(x:Fin 2→E4)(o:E4)(v:Fin 2→S.Field 4):
    Q.packet m (lift x) (d:=fun _:↥near=>4) (lift v) o =
    Q.packet m x (d:=fun _:Fin 2=>4) v o:=by
  unfold Reader.packet
  exact Finset.sum_congr rfl (fun j _=>congr_arg _ (Q.fresh_perm j x o (d:=fun _:Fin 2=>4) v nearIndex))

def defect (e:ℕ)(x:Fin 2→E4)(u:Fin 2→S.Field 4) (Y:S.Field 4) (z:E4) : S.Field e →ₗ[ℂ] ℂ :=
  upon S e z x (e:=fun _:Fin 2=>4) u -
    upon S e z (sole 0) (sole Y:Labels S (fun _:Unit=>4))

theorem signed {e:ℕ}(x:Fin 2→E4)(u:Fin 2→S.Field 4)(z:E4)(w:S.Field e)
    (separated:Injective (beside x (sole z))) (exterior:Injective (beside (sole (0:E4)) (sole z))):
    formula F Q (lift x) 0 (d:=fun _:↥near=>4) (lift u) (sole z) (sole w:Labels S (fun _:Unit=>e)) 4 none =
    defect (S:=S) e x u (Q.packet 4 x (d:=fun _:Fin 2=>4) u 0) z w:=by
  let b:Labels S (fun _:Unit=>e):=sole w
  let W:=Q.packet 4 x (d:=fun _:Fin 2=>4) u 0
  rw [formula,←packet_read F Q _ _ _ _ _ none 4 exterior,grouped F Q]
  change whole S (lift x) (lift u) (sole z) b-upon S 4 0 (sole z) b W=_
  have all:whole S (lift x) (d:=fun _:↥near=>4) (lift u) (sole z) b=
      whole S x (d:=fun _:Fin 2=>4) u (sole z) b:=
    whole_perm S (d:=fun _:Fin 2=>4) nearIndex (Equiv.refl Unit) Q.continuum separated
  rw [all]
  change _-whole S (sole 0) (sole W:Labels S (fun _:Unit=>4)) (sole z) b=
    whole S (sole z) b x (d:=fun _:Unit=>e) u-whole S (sole z) b (sole 0) (sole W:Labels S (fun _:Unit=>4))
  rw [whole_flip u b x (sole z) Q.continuum separated,whole_flip (sole W:Labels S (fun _:Unit=>4)) b (sole 0) (sole z) Q.continuum exterior]

end YM.Integration.WilsonCenteredFourSpatialNodes
