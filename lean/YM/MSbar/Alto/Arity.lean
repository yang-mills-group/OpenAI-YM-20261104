import YM.MSbar.Alto.Textile
import YM.PCalc.Band
import YM.MSbar.Chord.Locks
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Alto
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Parma Tin Bronze Asymptotics Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}
open Supply Input
variable {O:ChartRatio G}{K:MapPrices} {B: Sheet G}{D: Rolls B}{Θ:Protection D}{T:Delays Θ}{W: Bar T}{I:Wait W}{P:PostCost D}(A:Directed G I O K P)
-- knot condition
structure Merit (L:Levels G) (H:Horizon L) :Prop where
    towns : ∀ i p, Bid.Larger (G:=G) (L.clock.op i p)
    sworn : ∀ N m, m ≤ N → ∀ p:ℕ,Bid.Sworn (H.H N m) (L.S.side m p) G
local notation "B₀"=> A.kin
local notation "ℓ"=> A.a
set_option quotPrecheck false
local notation "Θ₀"=>A.a.clock
variable (j i m N k p:ℕ)
local notation "M!"=> (A.a.S.block m).val
local notation "g!"=> A.a.S.side m p
local notation "g'"=> A.a.S.side (m+1) p
local notation "e"=>A.a.clock.op m p
local notation "P'"=> (A.M.towers N m).A0
local notation "Y"=>Primary g! G
variable (F:Forest (A.a.clock.op m p).ratio) (h:Merit A.a A.M) (hm:m<N)
include h hm
local notation "D'"=> drift K j
local notation "α"=> ceilα K j i
variable (hv:A.a.clock.J (m+1)=j) (hi:A.a.clock.J m=i)
include hv hi
-- stance from Towers.DEEP stage
lemma stance (a':ℝ)(p':ℕ)(hh:0≤a')(ht:a'≤ceilα K j i)(hx:5≤j): Cane (g:=(A.a.clock.op m p).ratio) (A.M.towers N m).A0 (drift K j) (K.α j) a' (widthP K j p') 3 p' :=by -- implicit g not inferred Cane?
   let β:=K.α j; have hk:= low_earns _ p' (show 0 < K.α j/4 from (by have he:= K.alpha_pos j;positivity)); have hp:= cone_pos K j; unfold widthP
   refine ⟨hh,K.alpha_pos _, ?_, hp,hk.1,fun s hs=>?_ , fun l hi=>?_,(A.a.clock.op m p).patch.odd_side⟩ -- low bound from sufficient real not Nat; `widthP` low gives Nat only. redesign
   · have hx := ht.trans (le_trans (min_le_right (1:ℝ) _) (min_le_left _ (K.α i/2))); linarith only [hx]
   · exact hk.2 s hs -- type
   have he:=(A.plan.costs N m hm); rw [hv] at he; have hx:= he.2.2.2 l (by omega); exact Work.F08.strip_mono hx.1 le_rfl (div_le_div_of_nonneg_right (by unfold drift; linarith only [le_abs_self (K.Ω j)]) (by positivity)) -- choose type
end YM.MSbar.Alto
