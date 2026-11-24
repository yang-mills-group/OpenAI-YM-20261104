import YM.OPE.Beams.Rock
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
local notation "K!"=> (fun i=> A i univ *fuel (R i) H n (e+1)/(R i 0)^w.fst)
include L' V P' h U hY B H' hz hm hη
lemma plenary (hX:∀ᶠ i in f,draft Q (R i) (r i) M η H (X i)) : Wallet f T (fun i=> (K! i:ℝ) • (Y.ope w (X i) p (z i)-paidStep Y w p U' (X i) (z i) e)):=by
    let M':=M+η/2; let k':= 1+ 8*M'; let k:= Q.star; have ht:= half_pos hη; have hM':0≤ M':=add_nonneg hm ht.le; obtain ⟨D',hD'⟩:= Border.prizes P' B (P:=k') (by unfold k'; linarith only [hM']); let y(i:L) (u:I→ E4):= Y.ope w u p (z i); let G(i:L)(u:I→ E4):=(K! i:ℝ) • (y i u-paidStep Y w p U' u (z i) e); have hl:= H'.exists_.symm.le; have hT:= B.life; have hZ:= (B.ahead (Nat.zero_le _)); have hx₀:= Shuttle.soon hD' (Nat.zero_le _) hz; let F(i:L)(u:I→ E4):= ξ! i u
    apply rolling (W:=G) hD' hl hm hη hX
    · have hf:= slender_lane B hl hm hη hX; have hs:= slender_main B H' hm hη hX; have hw : Lent (f:=f) (T:=T) (F:=fun i z'=> paidStep Y w p U' (F i z') (z i) e):=by
          unfold paidStep; apply Lent.sum hT; intro a ha; let Y_c:(↑(Q.focus H):Type)→I:=fun i=>i.val; exact ((hf.relabel Y_c Subtype.val_injective).on U hT (chunk U' p) k a Y (o:=fun i=>(0:E4)) (tendsto_const_nhds.congr (fun i=>(norm_zero ..).symm ))).mul (hs.on U hT _ k w Y hx₀)
      apply ((hf.on U hT p k w Y hx₀).sub hT hw).scaled hT; exact ((((onsetFee p B univ).mul (((B.ahead (H'.before.le.trans H'.atMost)).div (B.ahead H'.atMost)).power (e+1))).div (hZ.power w.fst)).pays hT)
    intro x hx
    have hv : ∀ᶠ i in f, ‖z i‖ ≤ R i 0*M':=by filter_upwards [hz,hZ.pos] with i hi he using hi.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ht.le) he.le)
    exact Rock.along_grid (x:=x) U B H' hM' ht p hv P' w h L' V hY hD' (by unfold k'; linarith only) (hx.mono fun i hi=>hi.1) (hx.mono fun i hi=> hi.2) e
end YM.OPE.Log.Reels
