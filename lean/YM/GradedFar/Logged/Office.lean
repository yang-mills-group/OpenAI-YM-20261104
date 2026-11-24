import YM.GradedFar.Logged.Synthesis

/-!
# Expanded physical cost including every slot
Given the estimates on their common actual H
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Logged.Office
open Finset Filter Function Set Spec Table Extraction OPE.Log Asymptotics Orbits MeasureTheory
open scoped Topology Classical BigOperators ContDiff
open Seats Stroke Fork Deck Synthesis Subtable
open Economy (Paint)
variable {I J L:Type} [Fintype I][Fintype J]
variable (D : Pitch L)
variable (x:L→I→E4)(y:L→J→E4)(o:L→E4) (M δ:ℝ)
  (hm:0 ≤ M)(hd:0<δ) (hx:∀ᶠ i in D.p, Landed (D.r i) (D.s i) M δ (x i) (y i))
variable {G:Gauge}{C:Family G}{f:Order}{S:Table C.book}(F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {d:I→ℕ}{e:J→ℕ} (v:L→Labels S d)(w:L→Labels S e) (u:L→Viewers F) (P:LogTrace F R.port) (simple:G.Simple) (h:ℕ)
local notation "X"=> inlay D x o
local notation "Y"=> outlay D y o
local notation "Q"=> F.sector.derivatives
local notation "T"=>spectator F
local notation "R0"=> Rnow D d e
local notation "s"=>D.s
local notation "r"=>D.r
local notation "stamp"=>D.toSmall

private lemma self_hook (u:Labels S d): current F (d:=d) le_rfl u=u:= funext fun j=>(F.sector.derivatives.arrival F.room.kernel.laws.toSymmetric F.phase.transport.injection ..)

variable (hv:Samples F R D.toSmall D.r d v)(hw:Samples F R D.toSmall D.s e w)
local notation "HZ"=>radius D h
abbrev total (i:L) := Orbits.whole (T (u i)) (X i) (v i) (Y i) (w i)
abbrev actorD (i:L) (a:S.Field h) := Orbits.upon (T (u i)) h (o i) (Y i) (w i) a
abbrev total_gap (i:L) := total D x y o F v w u i - actorD D y o F w u h i (R.packet h (X i) (v i) (o i))
def receipt (u:L→ Viewers F)(d:I→ℕ)(e:J→ℕ) (i:L) : Span S d e ℂ :=
    moment (T (u i)) (beside (X i) (Y i))
lemma rent_true (q: Viewers F)(i:L)(v:Labels S d)(w:Labels S e) :
    receipt D x y o F (fun _=> q) d e i (stages v w) = Orbits.whole (T q) (X i) v (Y i) w:=rfl

section
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E]
include hx hm hd P simple hv hw
lemma rated : Paint stamp (fun i=>1+HZ i) (total D x y o F v w u) := by
    apply Synthesis.combine F R (fun i=>1+HZ i) D (receipt D x y o F u) v w hv hw _ _ _ -- use direct
    · intro d' h; filter_upwards [hx] with i hi v w; have hc := indebted F (u i) h (show e≤e from le_rfl) v w (Fork.unique_part hi (o i) hd); rw [self_hook F w] at hc; exact hc
    · intro d' e' hd' hd''; filter_upwards [hx] with i hi v w; have hc:= indebted F (u i) (show d'≤d' from le_rfl) hd'' v w (Fork.unique_part hi (o i) hd); rw [self_hook F v] at hc; exact hc
    exact fun d' e' hd' he u' v'=> Zones.full_priced D x y o M δ hm hd hx F R u' v' u P simple h
lemma phased : Paint stamp s (fun i=> total D x y o F v w u i - total D x y o F v w (fun _=>none) i) := by
    let A d' e' (i:L):=receipt D x y o F u d' e' i-receipt D x y o F (fun _=>none) d' e' i
    apply Synthesis.combine F R D.s D A v w hv hw _ _ _
    · intro d' h; filter_upwards [hx] with i hi v w
      have H (j:Viewers F): whole (T j) (X i) (current F h v) (Y i) w= Orbits.whole (T j) (X i) v (Y i) w:=by
        have hh:= indebted F j h (show e≤e from le_rfl) v w (Fork.unique_part hi (o i) hd); rwa [self_hook] at hh
      exact congrArg₂ (·-·) (H _) (H _)
    · intro d' e' h h'; filter_upwards [hx] with i hi v w
      have H (j:Viewers F): whole (T j) (X i) v (Y i) (current F h' w)= Orbits.whole (T j) (X i) v (Y i) w:=by
        have hh:= indebted F j (show d'≤d' from le_rfl) h' v w (Fork.unique_part hi (o i) hd); rwa [self_hook] at hh
      exact congrArg₂ (·-·) (H _) (H _)
    exact fun d' e' hd' he u' v'=> phase D x y o M δ hm hd hx F R u' v' u P simple
lemma replaced : Paint stamp HZ (total_gap D x y o F R v w u h):= by
    let A d' e' i:= receipt D x y o F u d' e' i - packetM F R (u i) h (o i) (X i) (Y i) d' e'
    have H {d' e'} i (v : Labels S d')(w:Labels S e') : A d' e' i (stages v w)= Zones.A D x y o F R v w u h i := by
        unfold A; rw [MultilinearMap.sub_apply, booked]; rfl
    have book i : total_gap D x y o F R v w u h i=A d e i (stages (v i) (w i)):= Eq.symm (H ..)
    refine Paint.assists (Synthesis.combine F R HZ D A v w hv hw ?_ ?_ ?_) (.of_forall fun i=> (book i).symm)
    · intro d' hL; filter_upwards [hx] with i hi v w
      rw [H,H]; unfold Zones.A discrepancy
      have ht:= indebted F (u i) hL (show e≤e from le_rfl) v w (Fork.unique_part hi (o i) hd)
      rw [self_hook] at ht
      exact congrArg₂ (·-·) ht (DFunLike.congr_arg (upon (T (u i)) h (o i) (Y i) w) (packet_included F R h v hL (X i) (o i)))
    · intro d' e' hd' he'; filter_upwards [hx] with i hi v w
      rw [H,H]; unfold Zones.A discrepancy
      have ht:=indebted F (u i) (show d'≤d' from le_rfl) he' v w (Fork.unique_part hi (o i) hd)
      rw [self_hook] at ht
      exact congrArg₂ (·-·) ht (upon_any F (u i) he' h (R.packet h _ v (o i)) w (Fork.unique_root hi (o i) hd))
    intro d' e' hd' he' u' v'; simp_rw [H]; exact Zones.fresh_paid D x y o M δ hm hd hx F R u' v' u P simple h
omit hw simple in
lemma paid_packet : Paint stamp (fun i=>D.r i^h) (fun i=>R.fresh h (X i) (o i) (v i)) :=
   Synthesis.array F R _ D.toSmall.positive (fun d' i=>R.fresh h (X i) (o i) (d:=d')) v hv (fun d' hd=> Eventually.of_forall fun i u=>R.fresh_inclusions ..) (fun d' hd' v=> Trace.current F R stamp hm hd (X) o (whole_room D x y o M δ hm hd hx) P v h)

end
end YM.OPE.Logged.Office

