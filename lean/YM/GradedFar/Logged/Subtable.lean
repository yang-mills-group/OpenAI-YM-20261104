import YM.GradedFar.Logged.Zones
import YM.OPE.Orbits.Inclusions
import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# Same Table Orbits rows (towards log horizon) under cap mixing
Mark the multilinear nature & unmix expansions at each fixed finite cap, no height drift.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Logged.Subtable
open Function Filter Finset Set Spec Table Extraction Orbits
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Order}{S:Table C.book}(F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {I J:Type}[Fintype I][Fintype J]{d d':I→ℕ}{e e':J→ℕ}
local notation "Q"=>F.sector.derivatives
-- Same proof as Inclusion_slot extension `YM/AllOrder/Leading/Solve.moment_inclusion` (large import)
private lemma asFinite {n:ℕ}(v:Viewers F){d e:Fin n→ℕ}(h:d≤e)(u:Labels S d){y:Points n}(hy:y∈conf n):
    S.useAt (spectator F v) y (tags (fun i=> F.sector.derivatives.rise (h i) (u i)))= S.useAt (spectator F v) y (tags u) := by
  let W:=S.useAt (spectator F v) y; let t(c : Finset (Fin n)) i := if i∈c then tags (fun i=> F.sector.derivatives.rise (h i) (u i)) i else tags u i
  suffices H:∀ c:Finset _, W (t c) = W (tags u) from by simpa only [t,Finset.mem_univ,↓reduceIte] using H Finset.univ
  intro c; induction c using Finset.induction_on with
  | empty=>simp only [t,Finset.notMem_empty, ↓reduceIte]
  | insert i c hi ih=>
    rw [← ih,show t (insert i c) = update (t c) i ⟨e i,F.sector.derivatives.rise (h i) (u i)⟩ from
      (by funext j; by_cases h:j=i <;> simp [h,t,tags])]
    convert F.sector.derivatives.inclusion_slot (spectate_ready F v) (spectate F v).laws.toSymmetric (h i) hy i (t c) (u i) using 1; congr 1
    funext j; by_cases h:j=i <;> simp [h,t,tags,hi]

abbrev current (F:Final C f S) (h:d≤d')(u:Labels S d):Labels S d':= fun i=> F.sector.derivatives.rise (h i) (u i)
lemma moments (u:Labels S d)(s:Viewers F)(h:d≤d'){x:I→E4}(hx:Injective x):
    moment (spectator F s) x (current F h u)=moment (spectator F s) x u :=
    asFinite F s (d:=d ∘ runNames I) (fun i=> h (runNames I i)) (fun i=>u (runNames I i)) (y:=points (x∘runNames I)) (runs_conf.mpr hx)
lemma indebted (s:Viewers F)(h:d≤d')(he:e≤e')(u:Labels S d)(v:Labels S e) {x:I→E4}{y:J→E4}(hx:Injective (beside x y)) : whole (spectator F s) x (current F h u) y (current F he v)= whole (spectator F s) x u y v:= by
    unfold whole; have hh:Sum.elim d e ≤ Sum.elim d' e':= fun i=> by cases i with| inl i=> exact h i| inr i=>exact he i
    rw [show stages (current F h u) (current F he v)=current F hh (stages u v) from funext fun i=> by cases i <;> rfl, moments F _ _ hh hx]
lemma upon_any (s:Viewers F)(he:e≤e')(q:ℕ)(u:S.Field q)(v:Labels S e) {o:E4}{y:J→E4}(hy:Injective (beside (sole o) y)) :
    upon (spectator F s) q o y (current F he v) u = upon (spectator F s) q o y v u := by
    let x: Labels S (fun _:Unit=>q):=sole u
    have hx:= indebted (d:=fun _:Unit=>q) F s (fun _=> le_rfl) he x v hy
    rw [show current F (d:=fun _:Unit=>q) (fun _=> le_rfl) x = x from funext fun i=> F.sector.derivatives.arrival F.room.kernel.laws.toSymmetric F.phase.transport.injection (x i)] at hx; exact hx
lemma packet_included (q:ℕ) (u:Labels S d) (h:d≤d') (x:I→E4)(o:E4): R.packet q x (current F h u) o=R.packet q x u o:= by unfold Reader.packet; exact Finset.sum_congr rfl (fun i _=> congrArg (F.sector.derivatives.rise (d:=i.val) (Nat.le_of_lt_succ i.isLt)) (R.fresh_inclusions ..))


def packed (h:ℕ)(x:I→E4)(o:E4)(d:I→ℕ): MultilinearMap ℂ (fun i=>S.Field (d i)) (S.Field h) :=
    ∑ j:Fin (h+1), (F.sector.derivatives.rise (d:=j.val) (Nat.le_of_lt_succ j.isLt)).compMultilinearMap (R.fresh j.val x o)
lemma earned_pack (h:ℕ)(x:I→E4)(o:E4)(v:Labels S d): packed F R h x o d v=R.packet h x v o := by unfold packed Reader.packet; rw [_root_.sum_apply]; rfl

private def actor_f (i: Viewers F)(q:ℕ) (o:E4)(y:J→E4)(e:J→ℕ) : S.Field q →ₗ[ℂ] MultilinearMap ℂ (fun j=>S.Field (e j)) ℂ :=
    let P:=moment (spectator F i) (d:=Sum.elim (fun _:Unit=>q) e) (S:=S) (beside (sole o) y)
    P.currySum.toLinearMap 0 ()
private lemma entry (i:Viewers F)(q:ℕ)(o:E4)(u:S.Field q)(y:J→E4)(v:Labels S e) : actor_f F i q o y e u v= upon (spectator F i) q o y v u:= by
    let P:=moment (spectator F i) (d:=Sum.elim (fun _:Unit=>q) e) (S:=S) (beside (sole o) y)
    let L:Labels S (fun _:Unit=>q):= update (fun _=> (0:S.Field q)) () u
    change P (Sum.rec L v)= _; change _= P (stages (d:=fun _:Unit=>q) (sole u) v); apply congr_arg; funext j; rcases j with ⟨⟩|j; · exact Function.update_self ..
    rfl

/-- Build M.L with exactly the substituted position and viewer used in Q.packet.
No condition even required when computing it, but physically it will be used ONLY
on Injective beside .. -/
def packetM (i: Viewers F)(q:ℕ)(o:E4)(x:I→E4)(y:J→E4) (d:I→ℕ)(e:J→ℕ):
    MultilinearMap ℂ (fun j=> S.Field (Sum.elim d e j)) ℂ :=
    MultilinearMap.currySumEquiv.symm ((actor_f F i q o y e).compMultilinearMap (packed F R q x o d))
lemma booked (i:Viewers F)(q:ℕ)(o:E4)(x:I→E4)(y:J→E4)(v:Labels S d)(w:Labels S e):
    packetM F R i q o x y d e (stages v w) = upon (spectator F i) q o y w (R.packet q x v o) := by
    rw [← entry F i q o, ← earned_pack F R q x o]; rfl
end YM.OPE.Logged.Subtable
