import YangMills.WilsonProof.NativeSupport.Commissioned259.Horizon.Compact
import YM.OPE.Orbits.Inclusions
/-!
# use exactly Rise on these physical fields; via moment inclusion theorem clone
from `YM/OPE/Levy/Measured.lean`. "$Reader$ inclusions" is on actual R, on these prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flash259HorizonFork
open Function Filter Set Asymptotics MeasureTheory Table Extraction Spec Arboreal OPE.Orbits
open scoped Topology Classical BigOperators
open Node Log
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(U:Final C f S)
local notation "V" => U.sector.derivatives
lemma freeze {I E B:Type*}[Fintype I][DecidableEq I](f:(I→E)→B)(x y:I→E)
   (hf:∀ i t, f (Function.update t i (x i))=f (Function.update t i (y i))):f x=f y:=by
     classical
     let g(s:Finset I)(i:I):= if i∈s then x i else y i
     have hid (s:Finset I): f (g s)= f y:=by
         induction s using Finset.induction_on with
         | empty=> simp_rw [g,Finset.notMem_empty,ite_false]
         | @insert i b hi ih=>
              have h':∀j,j≠i→ g (insert i b) j=g b j:=fun j he=>by simp [g,he]
              rw [show g (insert i b) = update (g b) i (x i) from ?_,hf,← ih]; apply congr_arg
              · apply funext; intro j; by_cases hh : j=i; swap; exact update_of_ne hh ..
                subst j; simp [g,hi]
              funext j; by_cases hh : j=i; subst j; · simp [g,update_self]
              rw [update_of_ne hh,h' j hh]
     rw [← hid Finset.univ]; simp [g]

lemma inclusionMoment {I:Type}[Fintype I] (d h₁ : I→ℕ)(he:d ≤ h₁)(v:Labels S d)
   (x:I→E4)(q:Viewers U)(hx:Injective x) :
   Orbits.moment (spectator U q) x v = Orbits.moment (spectator U q) x (fun i=>(V).rise (he i) (v i)) := by
      let T₁:=spectator U q
      rw [Orbits.observed,Orbits.observed]
      exact freeze (OPE.observe T₁ x) _ _ (fun i w=>(observe_replace T₁ w (spectate U q).laws.toSymmetric (spectate_respects U q) (spectate_ready U q) hx i (he i) (by unfold Orbits.names; erw [S.rep,S.rep])).symm)


variable {I J : Type} [Fintype I] [Fintype J] {d e : I→ℕ} {c : J→ℕ} (p : Viewers U)
abbrev promote (U:Final C f S) {d e : I→ℕ} (h : d ≤ e) (u: Orbits.Labels S d) : Orbits.Labels S e := fun i => U.sector.derivatives.rise (h i) (u i)
lemma lite {x:I→E4} {y:J→E4} (h:Function.Injective (beside x y)) (e0:d ≤ e) (u: Labels S d)(v:Labels S c) :
    Orbits.whole (spectator U p) x (promote U e0 u) y v=Orbits.whole (spectator U p) x u y v:=by
  have H : Sum.elim d c ≤ Sum.elim e c := fun i=> by cases i with
    | inl j=>exact e0 j
    | inr j=>exact le_rfl
  rw [Orbits.whole,Orbits.whole,inclusionMoment U _ _ H (stages u v) (beside x y) p h]; congr 1; funext i; cases i with
  | inl i=> rfl
  | inr i=> exact ((V).arrival U.room.kernel.laws.toSymmetric U.phase.transport.injection (v i)).symm
lemma far_lite {x:J→E4}{y:I→E4} (h:Function.Injective (beside x y)) (e0:d ≤ e) (u:Labels S c)(v:Labels S d):
    Orbits.whole (spectator U p) x u y (promote U e0 v)=Orbits.whole (spectator U p) x u y v:=by
  rw [ ← whole_flip u _ x y (spectate U p) h,←whole_flip u v x y (spectate U p) h]; apply lite U p _ e0
  exact beside_distinct.mpr (by obtain ⟨hi,hj,h⟩:= beside_distinct.mp h; exact ⟨hj,hi,fun i j=>(h j i).symm⟩)
lemma packet_rises (Q:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin) (e0:d ≤ e) (u:Labels S d) (x:I→E4) (o:E4) (h:ℕ):
    Q.packet h x (promote U e0 u) o=Q.packet h x u o := Finset.sum_congr rfl (fun j _=> congr_arg (U.sector.derivatives.rise (Nat.le_of_lt_succ j.isLt)) (Q.fresh_inclusions e0 x o j.val u))
end YM.OPE.Flash259HorizonFork
