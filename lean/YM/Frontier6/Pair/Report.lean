import YM.Frontier6.Pair.Trains
import YM.Work.B03
import YM.Work.B04

/-! Group EP bounds preserve **every** character. Reporting is in compound-word
expectations (not multiplicative on spatial slots). -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6
open Set Filter Function MeasureTheory Lattice Cells Wilson Extraction Spec Bid Work.B15 Next.UVStress OS OS.Ground
open scoped Topology BigOperators InnerProductSpace
variable {G : Gauge} {C : Family G} {S : Table C.book} {F : Extraction.Order}
variable (K: Spec.Final C F S)

abbrev StateIndex := Option K.α.space.X
def state : StateIndex K → Table C.book
 | none=>S
 | some z=> K.α.ensemble z

lemma hierarchy (s:StateIndex K) : (state K s).Hierarchy:=by
   cases s; exact K.room.kernel; exact K.phase.phase.states _
lemma respects (s:StateIndex K) : (state K s).respects S:=by
   cases s with
   | none => exact fun _=>le_refl _
   | some s=> exact fun i=>(K.phase.phase.retains s i).symm.le
lemma inception (s:StateIndex K) : K.sector.derivatives.Inclusions (state K s):=by
   cases s; exact K.phase.transport.injection; exact K.phase.phase.coordinates _
lemma directional (s:StateIndex K) : K.sector.derivatives.Derivatives (state K s):=by
   cases s; exact K.phase.transport.derivatives; exact K.phase.phase.calculus _
lemma turn_state (s:StateIndex K) : K.sector.turns.Oriented (state K s):=by
   cases s; exact K.phase.transport.motion; exact K.phase.phase.sym _

namespace Platform
variable {I:Type*}[Fintype I] {k b:ℕ} (E: Episode C F k)
def fieldWord (E: Episode C F k)(T:Table C.book) := ∑ i:Fin E.num, E.factor i * T.expect (E.word i)
set_option quotPrecheck false
local notation "Ω"=>K.α.space
lemma phase_word (z : K.α.space.X):
   (Ω).character z (E.cluster K.α.unselected)=fieldWord E (state K (some z)):=by
   unfold Episode.cluster fieldWord
   let A:= K.α.unselected; let a:= K.α.space.character z
   -- respects
   rw [map_sum]; refine Finset.sum_congr rfl fun i _=>?_
   exact (Retain.picky A K.α.space z _ _).trans (congr_arg (E.factor i * ·) (Retain.pops A K.α.space (K.phase.phase.chosen z) _ ((Word.realized _ _).2 (generic_conf _ (E.gen i)))))

open Org in
lemma lectern (K:Spec.Final C F S)(E:Episode C F k)(u:I→Cover)(hu:Injective u)(s:StateIndex K)
    {ℱ:Filter (ℕ×ℕ)} [ℱ.NeBot] (hs: Grill C F) (hk:b ≤ k) (h:ℱ ≤ F.fuse) (ε:I→ℝ) (hε:∀ i,0 ≤ ε i)
    (hp:∀ᶠ i:ℕ×ℕ in ℱ, SplitBoard (C:=C) b i.1 i.2 (E.cuts i.1 i.2 0) u ε) : ‖fieldWord E (state K s)‖ ≤ ∏ i, ε i:=by
   let A:= K.α.unselected; let V:= K.α.room; have hv: Steady V:= K.phase.phase.still
   have ht:Theme V A:=Work.B03.answer K.room.kernel _ _ _ hv K.phase.phase.lengths
   have hD:= K.phase.phase.decomposition
   have hX(z):= board_character E u hu hk K.α.space z K.room ht hv (Work.B05.answer Work.B04.answer K.room hs _ K.phase.transport V A hv ht) hD h ε hε hp
   simp_rw [phase_word K] at hX
   cases s with
   | some z=> exact hX z
   | none=>
     have hi (i:Fin E.num) : Continuous (fun z=> (state K (some z)).expect (E.word i)):= by
        have he:Word.distinct (E.word i):= Word.realized _ _ |>.2 (generic_conf _ (E.gen i)); exact (hD.weak (M A _ he)).congr (fun z=>Retain.pops _ _ (K.phase.phase.chosen z) (E.word i) he)
     let _:= hD.normalized
     have hP : (∫ z, fieldWord E (state K (some z)) ∂K.α.space.μ)=fieldWord E S:=by
        unfold fieldWord; rw [integral_finsetSum]; rotate_left; exact fun i _=> ((hi i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul _
        simp_rw [integral_const_mul]; exact Finset.sum_congr rfl (fun i _=>congr_arg (E.factor i * ·) (Spread.Resolution.barycenter K.α.space K.α.ensemble hD K.phase.phase.chosen K.room.kernel.translations _ ((Word.realized _ _).2 (generic_conf _ (E.gen i)))))
     change ‖fieldWord E S‖ ≤ _; rw [← hP]
     exact le_trans (norm_integral_le_of_norm_le (integrable_const _) (Eventually.of_forall hX)) (by rw [integral_const]; simp)
end Platform
end YM.Frontier6
