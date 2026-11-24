import YM.MS.High.Drive
/-!
# Taking solutions coherent in each finite degree

Earlier step `past` preserves actual parameters, not just high-order estimates.
Use diagonal theorem across coupling order. Solving rank≤ from descending ranks
uses finite number initially prescribed, protecting all estimates beyond.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.High.Knobs
open Function Filter Set Finset Real Plane Wire Flux Domain LogTime LogTime.IntervalFamily Momentum
open Landau Detect Koszul Logarithm Color
open scoped Topology ContDiff
variable {G : Gauge} {h q v:ℤ} {r s d n:ℕ} {b : Bool} {U:ℕ→Type} {k:Knobs U G} {F' : Recount G} {P Q: Code U}
-- common rule rank and grade. `Conf` given predecessor test P, n not only later code. Assume raising attainable hypothesis moves on slice; explicit production later.
def prepare (b:Bool) (k : Knobs U G) (P:Code U) (n:ℕ) (Q:Recount G) (d :ℕ) (h : ℤ) := EarlierOrder b (k.wake P) Q h d n

section
variable {B : Code U → Recount G} {L : Recount G} {C:ℂ}
    (R : ∀ X: Code U, Spheres wave (spaceL G) (B X) (k.wake X) C d b)
    (S : Spheres id (spaceD G) L F' C d b) (hF: Good b G h F')
    (hX : ∀ X:Code U,Rising b (k.wake X)) (hY:Rising b F')
-- predecessor B-independent compar or identifications
variable (rises: ∀ X:Code U,∀ n≥d, prepare b k X n F' d h → ∀ i∈paths n d,∀ s,Trust true 4 (B X (n-i)) (L (n-i)) (s+1)) (hp:h≥0)
-- bank of single-step changes; hypotheses for this helper lemma is ability to MOVE exactly on target slices; not final contract. Weak property filled from menu via class. Include fixed
variable (A : ∀ n ≥ d,∀ r, fig b r→∀ u:ℤ, 0≤u→u≤h→∀ X:Code U, Earlier (B X) L (k.wake X) F' b h n d r → Absent (k.wake X n-F' n) b r u → ∃ Y, Move b k X Y n r u (slice (k.wake X n-F' n) b r u))
-- help across ranks
include rises
lemma earned (ht : Ahead b (k.wake P) F' h d n r) (hd : d≤n) : Earlier (B P) L (k.wake P) F' b h n d r := by
   refine ⟨fun i hv t=> ?_, rises P n hd ht.1, ht.2 (r+2) (by omega)⟩
   rw [paths,Finset.mem_Ico] at hv; exact ht.1 i hv.2 hv.1 (t+1) (fun _=> Nat.succ_pos _)
-- ascend grade.
include R S rises A
private lemma field_level (v:ℕ) (hv:v≤h+1) (hd:d≤n) (H:fig b r) (hq : Ahead b (k.wake P) F' h d n r): ∃ Q, Stroke b k P Q n r ∧ Absent (k.wake Q n-F' n) b r v := by
    induction v with
    | zero => exact ⟨P,Stroke.of_refl,zero_absent _⟩
    | succ v IH =>
        obtain ⟨Q,hQ,HH⟩:= IH (by omega)
        have he := earned rises (ahead hQ hq) hd
        obtain ⟨Y,hY⟩:= A n hd r H v (by omega) (by omega) Q he HH
        push_cast; exact ⟨Y,hQ.trans hY.toStroke, accept (B:=B) hd H R S hY he (by omega) HH⟩
include hp hF hX hY
private lemma reach_n {P:Code U} (H:d≤n) (r:ℕ) (hv:fig b r) (hh:Ahead b (k.wake P) F' h d n r) : ∃ Q, Stroke b k P Q n r ∧ Trust b h (k.wake Q n) (F' n) r:= by
   generalize he : (h+1).toNat=v; have he' : h+1=v:=by omega
   obtain ⟨Q,X,hK⟩:= field_level R S rises A v he'.ge H hv hh
   exact ⟨Q,X,terminal (R Q) S hF H hv (earned rises (ahead X hh) H) (hX Q) hY (he' ▸ hK)⟩
private lemma all_rank {P:Code U} (H:d≤n) (hv : prepare b k P n F' d h): ∃ Q, (∀ i<n,P i=Q i) ∧ prepare b k Q (n+1) F' d h:= by
   suffices he : ∃ Q, (∀ i<n,P i=Q i)∧ prepare b k Q n F' d h ∧ ∀ r,fig b r→Trust b h (k.wake Q n) (F' n) r from ?_
   · obtain ⟨Q,hp,hq,hr⟩:=he; refine ⟨Q,hp,fun i hi hV r ht=>?_⟩; by_cases he:i=n; subst i; exact hr r ht; exact hq i (by omega) hV r ht
   obtain ⟨g,hP⟩:= (R P).rank n; obtain ⟨f,hQ⟩:= S.rank n
   let N:=f+g
   have hZ (r:ℕ) (hv:r≤N) : ∃ Q, (∀ i<n,P i=Q i)∧Ahead b (k.wake Q) F' h d n r:= by
       induction hv using Nat.decreasingInduction with
       | self=>
           refine ⟨P,fun i hi=>rfl,(by assumption : prepare b k P n F' d h),fun j hj=>?_⟩
           refine zero_ext (fun t i hi hU => hP t i hi ?_) (fun t i hi hU=> hQ t i hi ?_) <;> unfold N at hj <;> omega
       | of_succ r h IH =>
           obtain ⟨W,hW,hk⟩:=IH; obtain ⟨Z,hF,hH⟩:= reach_n R S hF hX hY rises hp A H _ (fun _=> Nat.succ_pos r) hk
           have hx:=ahead hF hk
           refine ⟨Z,fun i hi=> (hW i hi).trans (hF.past i hi),hx.1, fun i hi=> ?_⟩
           rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hi) with h1|h1
           rw [← h1]; exact hH
           exact hx.2 i h1
   obtain ⟨Q,hq,hk⟩:= hZ 0 (Nat.zero_le N); by_cases he:fig b 0
   · obtain ⟨Q',hq',H'⟩:= reach_n R S hF hX hY rises hp A H _ he hk; obtain ⟨HX,HY⟩:= ahead hq' hk; refine ⟨Q',fun i hi=> (hq i hi).trans (hq'.past i hi),HX, fun r hr=>?_⟩; cases r with | zero=>exact H' | succ r=>exact HY _ (Nat.succ_pos _)
   exact ⟨Q,hq,hk.1,fun i hv=> hk.2 i (Nat.pos_of_ne_zero (fun h=> he (h ▸ hv)))⟩

lemma assigned (p : Code U) : ∃ P, Fixed (k.wake P) F' b h d:= by
   have hi n : ∀ P : Code U, prepare b k P n F' d h → ∃ Q,(∀ i<n,P i=Q i)∧ prepare b k Q (n+1) F' d h := by
       intro P hK; by_cases he:d≤ n; exact all_rank R S hF hX hY rises hp A he hK; exact ⟨P,fun _ _=>rfl,fun i hi he r hr=>by omega⟩
   choose X hx h1 using hi; let T : ∀ n,{P: Code U // prepare b k P n F' d h}:= fun n=> Nat.recOn n ⟨p,fun i hi he r hr=>False.elim ((Nat.not_lt_zero i) hi)⟩ fun n Q=> ⟨X n Q.val Q.property,h1 n Q.val Q.property⟩
   let P i:= (T (i+1)).val i; refine ⟨P,fun n he r hr=>?_⟩
   have hp i n (H: i<n): (T n).val i=P i:= by
       change i+1≤n at H; induction n,H using Nat.le_induction with
       | base=> rfl
       | succ j h IH=> exact (hx j (T j).val (T j).property i h).symm.trans IH
   rw [← k.stay (T (n+1)).val P n (fun i hi=> hp i _ (by omega))]; exact (T (n+1)).property n n.lt_succ_self he r hr
end
end YM.MS.High.Knobs
