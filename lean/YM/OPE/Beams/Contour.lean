import YM.OPE.Beams.Thin
/-!
# Whole-hol reconstruction by sampling, on any declared layers
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Reels
open Function Filter Finset MeasureTheory Lattice RG Wilson Metric Polar
open Trunk Rhythm Payments
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}{C:Family G} {F:Extraction.Order} {S:Table C.book}(U:Spec.Final C F S)
variable {I J L Z:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{f:Filter L}
    {T:L→ℝ}{M η P₀:ℝ}
    {X:L→ I→ E4}{x:L→ (I→ E4)→ J→ E4}
    {H t n m:ℕ}{Q: Rhythm I}
    {R r:L→ℕ→ℝ}{α:ℕ→ℝ}
    {P:L→Loom Q} {B:Border f T Q.limit R r α} (D:Oscars B P₀ P C)
local notation "X'"=> (I→ E4)
local notation "ξ!"=> Border.orbit Q H T r X
local notation "μ"=> Q.localTime H
variable (hh:H ≤ Q.age Q.star)(hm:0 ≤ M)(hη:0<η)(hX:∀ᶠ i in f,draft Q (R i) (r i) M η H (X i))
local notation "T!"=> C.S.gridPoint
set_option quotPrecheck false
local notation "κ"=> (fun i=> (P i).launch Q.limit)
variable {W:L→ (I→ E4)→ℂ} (w: I→ C.book.Token)
lemma onsetFee (B:Border f T Q.limit R r α)(s:Finset I) : RateIs f T (fun i=> priceSet Q s w (R i)) (∑ i∈s, ((w i).1:ℝ)* -α (Q.age i)):= RateIs.prod (fun i _=> (B.ahead (Q.bounded i)).power (w i).1) B.life
include D hX hh hη hm
lemma rolling (hp:Lent (f:=f) (T:=T) (F:=fun i z=> W i (ξ! i z)))
    (hf:∀ x:L→ I→ Cover,(∀ᶠ i in f,draft Q (R i) (r i) (M+η/2) (η/2) H (C.S.gridPoint (κ i) ∘ x i) ∧ Seated Q C (P i) (C.S.gridPoint (κ i) ∘ x i) H) → Wallet f T (fun i=>W i (T! (κ i) ∘ x i))) : Wallet f T (fun i=> W i (X i)):=by -- local notation name hygiene B.Q.P
    let g (i)(z:X'):= W i (ξ! i z); let k:= length I; have hT:= B.life; have he:= hp.varied Q.star; have hg:Wallet f T (fun i=>g i 0):=by
       apply price_mesh hT ((hT.eventually_ge_atTop 1).mono fun _ hi=> one_le_pow₀ hi) (Eventually.of_forall (fun i=> (show 1 ≤ length I from length_most))) he; intro x hx; obtain ⟨y,p,Hφ⟩:= Oscars.snaps (X:=X) D hh  (show 1 ≤ length I from length_most) x hx; let u i:= ξ! i (y i);
       have ht:∀ᶠ i in f,draft Q (R i) (r i) (M+η/2) (η/2) H (u i):=by filter_upwards [B.trajectory hh hX hη,Hφ] with i ht hi using ht (y i) hi.2.1
       have hp : ∀ᶠ i in f,T! (κ i) ∘ p i=u i:= Hφ.mono (fun _ hi=> hi.2.2.2); refine ⟨y, (hf p ((ht.and Hφ).mono (fun i ⟨hx, hi⟩=> ?_))).congr (hp.mono fun i hi=> congr_arg _ hi),Hφ.mono (fun i hi=> hi.1)⟩
       rw [hi.2.2.2]; exact ⟨hx,hi.2.2.1⟩
    apply hg.congr; filter_upwards with i; unfold g Border.orbit; rw [show Border.pitches Q H T r i 0=0 from funext (fun j=> by unfold Border.pitches; simp), Q.no_move]
-- wallet cost matching before any mint. If centering by rᵢ under sign layout in x continuity gain. 
variable [f.NeBot] (K:Mode U.sector.derivatives) {φ:Filter (ℕ×ℕ)}[φ.NeBot] (h:φ ≤ F.fuse)
    (L':Services C F S) {W' r' D'}(P':LogPackage C W' r' D')(V:MatrixTicket (C:=C) S U.sector.derivatives φ){Y:Prescription U.sector.derivatives}(hY:Y.Coherent)
    {z:L→ E4}
local notation "t!"=> (fun i=>priceSet Q univ w (R i)/(R i 0)^K.fst)
include U h V hY L' P'
omit D
lemma direct (B: Border f T Q.limit R r α) (hv:∀ᶠ i in f,‖z i‖ ≤ R i 0*M) : Wallet f T (fun i=> (t! i:ℝ) • Y.ope K (X i) w (z i)):=by
    let M':=M+ η/2; let k':= 1+8*M'; have ht:0 < η/2:=half_pos hη; have hM':0≤ M':= add_nonneg hm ht.le; obtain ⟨D',hD⟩:= Border.prizes P' B (P:=k') (by unfold k'; linarith only [hM']); have hP:= B.life; let Y':=t!; have hh':= (B.ahead (Nat.zero_le _)); let a:= Q.star; let g(i)(z':I→ E4):=(Y' i:ℝ) • Y.ope K z' w (z i)
    apply rolling (W:=g) hD hh hm hη hX; · exact ((slender_lane B hh hm hη hX).on U hP w a K Y (Shuttle.soon hD (Nat.zero_le _) hv)).scaled hP (((onsetFee w B univ).div (hh'.power K.fst)).pays hP) -- order
    intro x hx
    have hv':∀ᶠ i in f, ‖z i‖≤R i 0*M':=by filter_upwards [hv,hh'.pos] with i hi hR; exact hi.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ht.le) hR.le)
    exact Shuttle.survey U hD P' K h V L' hY w hM' (by unfold k'; linarith only) ht hv' (hx.mono (fun i hi=> hi.2)) hh (hx.mono (fun i hi=> hi.1))
end YM.OPE.Log.Reels
