import YM.OPE.Beams.Stand
/-!
# Ancestor reader controls sign step even on disparate scales

Repair the coalesced token by expanding the basis exactly. Charge ONE channel
beyond the horizon (finite layer), paying its vote after using the same physical
match and replacing each term inside the sponsor's cluster product. On final
coordinates the sign can be priced by exact geometry as well by hol reconstruction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Reels
open Function Filter Finset MeasureTheory Lattice RG Wilson Metric Polar
open Trunk Rhythm Payments Shuttle
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}{C:Family G} {F:Extraction.Order} {S:Table C.book}(U:Spec.Final C F S)
variable {I J L Z:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{f:Filter L}[f.NeBot]
    {T:L→ℝ}{M η P₀:ℝ}{v j k:I}
    {X:L→ I→ E4}{x:L→ I→ Cover}
    {H t n m:ℕ}{Q: Rhythm I} {e:ℕ}
    {R r:L→ℕ→ℝ}{α:ℕ→ℝ}
    (B:Border f T Q.limit R r α)
    (H':Q.Strike H n)(hm:0 ≤ M)(hη:0<η)(p:I→ C.book.Token) {z:L→ E4}(hz:∀ᶠ i in f,‖z i‖ ≤ R i 0*M)
    {W r' D}(P':LogPackage C W r' D) (w:Mode U.sector.derivatives) {φ:Filter (ℕ×ℕ)} [φ.NeBot] (h:φ ≤ F.fuse)
    (L':Services C F S)(V:MatrixTicket (C:=C) S U.sector.derivatives φ){Y:Prescription U.sector.derivatives}(hY:Y.Coherent)
set_option quotPrecheck false
local notation "X'"=> (I→E4)
local notation "ξ!"=> Border.orbit Q H T r X
local notation "μ"=> Q.localTime H
local notation "L!"=> U.sector.derivatives
local notation "U'"=> Q.focus H
local notation "A"=> (fun i b=> priceSet Q b p (R i))
abbrev scene (s:Finset I)(p:I→C.book.Token)(x:I→ E4)(t:C.book.Token):Unit⊕ (↑(univ \ s):Type) → C.book.Token:= beside (sole t) (chunk (univ\s) p)
noncomputable def paidStep {G:Gauge}{C:Family G}{S:Table C.book}{U:DiffPlan S} (Y:Prescription U) (w:Mode U)(p:I→ C.book.Token) (q:Finset I)(x:I→ E4)(z:E4)(m:ℕ):=∑ b∈ bands U m,Y.ope b (chunk q x) (chunk q p) 0 *Y.ope w (substituted q x) (beside (sole (Y.letter b)) (chunk (univ\ q) p)) z
local notation "K!"=> (fun i=> A i univ *fuel (R i) H n (e+1)/(R i 0)^w.fst)
-- scalar normalized product scale toolkit for inserting.S.Note.Flip.
private lemma discount_real (x y:ℂ)(a b:ℝ): (a • x)*(b • y)=(a*b) • (x*y):=by rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]
namespace Rock
include B hm hη H' hY U V P' hz L' h
local notation "M'"=> priceSet
local notation "F!"=> (fun i=> M' Q (remaining Q H) p (R i))
variable {D':L→Loom Q} (hc:Oscars B P₀ D' C)
local notation "V!"=> (fun i=> C.S.gridPoint ((D' i).launch Q.limit) ∘ x i)
include hc
lemma along_grid (hM:8*M<P₀) (hX:∀ᶠ i in f,draft Q (R i) (r i) M η H (C.S.gridPoint ((D' i).launch Q.limit) ∘ x i)) (ht:∀ᶠ i in f,Seated Q C (D' i) (V! i) H) (e:ℕ) : Wallet f T (fun i=> (priceSet Q univ p (R i)*fuel (R i) H n (e+1)/(R i 0)^w.fst:ℝ) • (Y.ope w (V! i) p (z i)- paidStep Y w p (Q.focus H) (V! i) (z i) e)):=by
    let g:=e+1; let F':= V!; let u:=remaining Q H; let P i:=priceSet Q univ p (R i)*fuel (R i) H n g/(R i 0)^w.fst; let Φ i:=A i (Q.focus H); obtain ⟨y,hp,hq⟩:= swipe U hc P' w h V L' hY p hm hM hη hz ht hX H' g
    let F_x i b:= Y.ope w (substituted (Q.focus H) (F' i)) (scene (Q.focus H) p (F' i) (Y.letter b)) (z i); -- binder f shadow!
    let ξ i b:= Y.test b g (S.project g (y i)); let φ i b:= Y.ope b (chunk U' (F' i)) (chunk U' p) 0; let X₀:= U'; let S':= bands L! g; let s:= bands L! e
    have he : s ⊆ S':= fun l hl=> (full_bands ..).2 (((full_bands ..).1 hl).trans e.le_succ); have hT:=B.life; have hr0:= (B.ahead (Nat.zero_le Q.limit)).pos; have hr := (B.ahead (H'.before.le.trans H'.atMost)).pos; have hR:= (B.ahead H'.atMost).pos
    have hf (b:Mode L!)(hh:b.fst ≤ g)(x:L→ℂ)(hp: Wallet f T (fun i=> (Φ i/R i H^g:ℝ) • x i)): Wallet f T (fun i=> (P i:ℝ) • (x i*F_x i b)):=by
        let Z_(i):= R i n ^ b.fst; have hh' := Echo.shifted U B H' hm hη hX p P' w h L' V hY (Y.letter b) hz; let d:= g-b.fst; have hX:= Wallet.from_tends (T:=T) hT (B.narrows n (H'.before.le.trans H'.atMost)); apply ((hX.pow hT d).smul (hp.mul hh')).congr; filter_upwards [hr,hR,hr0] with i hr hR hp; rw [discount_real,smul_smul]; change _ • (x i*F_x i b)= _; unfold Φ P d; congr 1; -- congr scalar s vs rhs
        rw [Echo.full (Q:=Q) p U']; have hh':R i n^g= R i n ^(g-b.fst)* R i n ^ b.fst:=(by rw [← pow_add,Nat.sub_add_cancel hh]); unfold fuel; rw [div_pow,hh']; change R i n^(g-b.fst)* (Φ i/R i H^g*(R i n^b.fst* _/R i 0^w.fst))= (Φ i * F! i)* _ / _; field_simp
    have hu(k:Mode L!) (he:k∈s) : Wallet f T (fun i=> P i • ((ξ i k-φ i k)*F_x i k)):=by
       have hp':k∈S':= ‹s ⊆ S'› he; apply hf k ((full_bands ..).1 hp') (fun i=>ξ i k-φ i k) ; apply (hq k hp'|>.1.neg).congr; filter_upwards with i; dsimp only [ξ,φ]; rw [← smul_neg,neg_sub]
    have hy (k:Mode L!) (ht:k∈ S' \ s):Wallet f T (fun i=> P i • (ξ i k*F_x i k)):=by
       obtain ⟨hf',he⟩:=mem_sdiff.mp ht; have he':k.fst=g:= le_antisymm ((full_bands ..).1 hf') (lt_of_not_ge (fun h'=>he ((full_bands ..).2 h'))); apply hf k he'.le (fun i=>ξ i k) ; have hh:= (hq k hf'|>.2); rw [he'] at hh; exact hh
    apply ((hp.add hT (Wallet.sum hT hy)).add hT (Wallet.sum hT hu)).congr; filter_upwards with i; let X_:=F' i; let p' := Y.ope w (substituted X₀ X_) (substituted_row X₀ p (y i)) (z i); let p₀:=Y.ope w X_ p (z i); change P i • (p₀-p')+(∑ j∈ S' \ s, P i • (ξ i j*F_x i j))+(∑ j∈s,P i • ((ξ i j-φ i j)*F_x i j))= P i • (p₀-paidStep Y w p X₀ X_ (z i) e); rw [show p'=∑ j∈ S',ξ i j*F_x i j from Prescription.phaseAtRows Y U.room.kernel.laws.toSymmetric U.phase.transport.injection hY w (y i) (0:E4) (z i) (chunk u X_) (chunk u p)]; -- rw at actual goal p' target expression won't find
    simp_rw [← smul_sum,← smul_add]; congr 1; unfold paidStep; change p₀-(∑ j∈ S',ξ i j*F_x i j)+(∑ j∈S'\s, ξ i j*F_x i j)+(∑ j∈s,(ξ i j-φ i j)*F_x i j)=p₀- ∑ j∈s,φ i j*F_x i j; rw [← sum_sdiff he]; simp_rw [sub_mul,sum_sub_distrib]; abel -- careful rw loops
end Rock
end YM.OPE.Log.Reels
