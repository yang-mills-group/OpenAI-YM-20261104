import YM.OPE.Orbits.Inclusions
import YM.OPE.Levy.Measured
import Mathlib.LinearAlgebra.Multilinear.Curry
/-!
# (G.6) API for physical multilinearity and grade promotion
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Fork
open Finset Filter Function Set Spec Table Extraction OPE OPE.Orbits
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    {I J:Type} [Fintype I] [Fintype J]
    {d:I→ℕ} {e:J→ℕ} (x:I→E4) (y:J→E4) (o:E4) (h:ℕ)
-- curried over both real Far and basis Near at any d and e. No Viewer sums yet.
variable (v : Viewers F) (P : Prescription F.sector.derivatives)
def trace := (Orbits.moment (S:=S) (d:=Sum.elim d e) (spectator F v) (beside x y)).currySum
lemma trace_apply (u:Labels S d)(w:Labels S e) : trace F x y v u w = whole (spectator F v) x u y w := by
  rw [trace, MultilinearMap.currySum_apply]; apply congrArg (Orbits.moment (S:=S) (d:=Sum.elim d e) (spectator F v) (beside x y)); funext j; cases j<;>rfl

def watch : S.Field h →ₗ[ℂ] MultilinearMap ℂ (fun i=> S.Field (e i)) ℂ where
  toFun p:= trace F (d:=fun _:Unit=>h) (sole o) y v (sole p)
  map_add' p q:= by
    ext w
    change trace F (d:=fun _:Unit=>h) (sole o) y v (sole (p+q)) w = trace F (d:=fun _:Unit=>h) (sole o) y v (sole p) w +
      trace F (d:=fun _:Unit=>h) (sole o) y v (sole q) w
    simp only [trace_apply]; exact (upon (spectator F v) h o y w).map_add p q
  map_smul' z p:= by
    ext w
    change trace F (d:=fun _:Unit=>h) (sole o) y v (sole (z • p)) w = z • trace F (d:=fun _:Unit=>h) (sole o) y v (sole p) w
    simp only [trace_apply]; exact (upon (spectator F v) h o y w).map_smul z p
lemma watch_apply (p:S.Field h)(w:Labels S e) : watch F y o h v p w = upon (spectator F v) h o y w p :=
  trace_apply (d:=fun _:Unit=>h) F (sole o) y v _ w

def view_shadow : MultilinearMap ℂ (fun i=> S.Field (d i)) (S.Field h) :=
  ∑ a∈ bands F.sector.derivatives h, (((LinearMap.id (R:=ℂ) (M:=ℂ)).smulRight (P.loaded a h)).compMultilinearMap (checkRow P a x o))
lemma view_shadow_apply (u:Labels S d) : view_shadow F x o h P u=shadowOld P h x o u := by
  rw [shadowOld,OPE.shadow,view_shadow,_root_.sum_apply]; apply Finset.sum_congr rfl; intro a _
  change (checkRow P a x o u) • P.loaded a h =_; rw [check_eq _ _ F.room.kernel]

def shadowError : MultilinearMap ℂ (fun i=> S.Field (d i)) (MultilinearMap ℂ (fun i=> S.Field (e i)) ℂ) :=
  trace F x y v - (watch F y o h v).compMultilinearMap (view_shadow F x o h P)
lemma shadowError_apply (u:Labels S d)(w:Labels S e) : shadowError F x y o h v P u w =
    discrepancy (spectator F v) h x o u (shadowOld P h x o u) y w := by
  change trace F x y v u w - watch F y o h v (view_shadow F x o h P u) w = _
  rw [trace_apply, view_shadow_apply, watch_apply, discrepancy]

lemma whole_include {d':I→ℕ} {e':J→ℕ}(hd:d≤d')(he:e≤e') (u:Labels S d) (w:Labels S e)(hx:Injective (beside x y)) :
    whole (spectator F v) x (fun i=>F.sector.derivatives.rise (hd i) (u i))
      y (fun j=> F.sector.derivatives.rise (he j) (w j)) = whole (spectator F v) x u y w := by
  have h : Sum.elim d e ≤ Sum.elim d' e' := fun i=> Sum.rec hd he i -- case needed
  unfold whole; rw [Levy.inclusionMoment F _ _ h (stages u w) _ v hx]; apply congrArg
    (Orbits.moment (S:=S) (d:=Sum.elim d' e') (spectator F v) (beside x y)); funext i; cases i<;>rfl
lemma upon_include {e':J→ℕ} (he:e≤e')(a:S.Field h)(w:Labels S e)(hx:Injective (beside (sole o) y)) :
    upon (spectator F v) h o y (fun j=> F.sector.derivatives.rise (he j) (w j)) a = upon (spectator F v) h o y w a := by
  let u : Labels S (fun _:Unit=>h) := sole a
  have hv : (fun i:Unit=> F.sector.derivatives.rise (d:=h) le_rfl (u i))= u := funext (fun i=> F.sector.derivatives.arrival
    F.room.kernel.laws.toSymmetric F.phase.transport.injection _)
  have hQ := whole_include F (sole o) y v le_rfl he u w hx; rw [hv] at hQ; exact hQ
lemma shadow_inclusion (H:P.Coherent) {d':I→ℕ}(hd:d≤d') (u:Labels S d) :
    shadowOld P h x o (fun i=>F.sector.derivatives.rise (hd i) (u i))=shadowOld P h x o u := by
  exact Finset.sum_congr rfl fun a _=> congrArg (fun c:ℂ => c • P.loaded a h)
    (Levy.freeze (fun p=> P.ope a x p o) _ _ (fun i w=> P.respectsLabel w H
      F.room.kernel.laws.toSymmetric F.phase.transport.injection i (hd i) (by unfold names; erw [S.rep,S.rep]) a))
lemma shadowError_inclusion (H:P.Coherent) {d':I→ℕ} {e':J→ℕ}(hd:d≤d')(he:e≤e') (u:Labels S d) (w:Labels S e)
    (hx:Injective (beside x y)) (hy:Injective (beside (sole o) y)) :
    shadowError F x y o h v P (fun i=>F.sector.derivatives.rise (hd i) (u i)) (fun i=>F.sector.derivatives.rise (he i) (w i))=
      shadowError F x y o h v P u w := by
  rw [shadowError_apply,shadowError_apply,discrepancy,discrepancy,whole_include F ..,shadow_inclusion F x o h P H,
    upon_include F y o h v he ..] <;> assumption

variable (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
def packetCost := -- not norm, actual fixed-basis multilinear packet
   ∑j:Fin (h+1), (F.sector.derivatives.rise (d:=j.val) (e:=h) (Nat.le_of_lt_succ j.isLt)).compMultilinearMap
      (Q.fresh (d:=d) j.val x o)
lemma packetCost_apply (u:Labels S d): packetCost F x o h Q u = Q.packet h x u o := by
  rw [packetCost,_root_.sum_apply]; rfl
lemma packet_inclusion {d':I→ℕ}(hd:d ≤ d') (u:Labels S d) :
    Q.packet h x (fun i=>F.sector.derivatives.rise (hd i) (u i)) o = Q.packet h x u o:=
  Finset.sum_congr rfl fun _ _=> congrArg _ (Q.fresh_inclusions ..)
end YM.Integration.GradedFar.Fork
