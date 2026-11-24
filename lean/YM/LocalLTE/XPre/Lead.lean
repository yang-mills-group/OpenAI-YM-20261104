import YM.LocalLTE.XPre.Tones
import YM.LocalLTE.Ticket.Prize
/-!
# Consuming all symbolizations issued by H at one label position
No φ equality across horizons. Repainting orbit uses true incoming evaluations.
Sum.Invariant.Same lamps.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.XPre
open Function Finset Filter Set MeasureTheory Lattice Wilson RG
open Extra.Histories Push Local Motion Extra.Multi
open LocalLTE.Fan LocalLTE.River LocalLTE.Vinca Ticket
open PhysicalNext.Repeat Lotus Blush Progress.DirectedRecipe
open YM.MergeProof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {ι: Type}{G:Gauge}{c f:Side}{S:StepData c f} {R : Rep G f} {C: Rep G c}
    {κ κ' K ν t u q r s b:ℝ} {A:Activities G f} {d t₀ p m l:ℕ} {o:Site f}{o':Site c}
open AbsoluteSums Animals Next.Foundations Source Planned.GuardedAtom
variable {v w:ℂ}{X Y:Set Wing}{M:ι→ Leaf R}{g:ι→ℂ}{φ:MergeProof.Response G c}{L:GaugeDoor R C}
variable {E:Config G f→ℂ} {Z: Res G f}{W : Res G c}
set_option quotPrecheck false
local notation "B'"=> localSection G d
local notation "F"=> ((Labels.frames G).level d)
local notation "φB"=> hol G
open Extra.Histories.InputColumn
variable {H:History G} {N n:ℕ} {L:GaugeDoor (H.rep N n (m+1)) (H.rep N n m)}
local notation "s'"=> H.S.side m n
local notation "s"=> H.S.side (m+1) n
local notation "R1"=> H.rep N n (m+1)
local notation "R0"=> H.rep N n m
local notation "κZ"=> Real.sqrt (H.levels.clock.forcedAllowance (m+1))
local notation "κI"=> Real.sqrt (H.levels.clock.forcedAllowance m)
local notation "HX"=> H.S.block m
local notation "v'"=> (((HX|>.val):ℂ)^d)
variable (d) (K: Guard.Keeper ((H.rep N n (m+1)).p) ((H.rep N n (m+1)).activities)) (U: Vinca.Gateway ((Labels.frames G).level d) (hol G) (H.rep N n (m+1)) (H.S.side m n)) (A: Prices)
variable {B: Heading ((Labels.frames G).level d)} {π c' d' w:ℝ}(hD: Vinca.Key (localSection G d) H N n m (hol G) L U c' π w B X)
include hD
variable (ha: ∀ i,Y (.gasKey (cart (R:=H.rep N n (m+1)) K i)))(ht:∀ i,X (.gasKey (cart (R:=H.rep N n (m+1)) K i)))(hq:0≤π)
variable (V:Voice ((Labels.frames G).level d) H n (m+1)) (T:Employ H N n (hol G) m V K)
variable (hV:SoundDoor (H.levels.clock.op m n) L) (hP : XPre.Permits (H.rep N n (m+1)) (H.rep N n m) Y L d ((((H.S.block m).val:ℂ)^d)) U A κ p l) (hb:Heard (localSection G d) H N n (hol G) (m+1) V)
local notation "pZ"=> κZ*(r+r)
local notation "feeE"=> A.beam+2*(ν+r+pZ)
local notation "x0"=> (H.levels.params (m+1)).columns
local notation "gnE"=> A.grant+A.canopy*(x0+pZ)
local notation "baseq"=> 2*(r+pZ)
-- stamina all X'. supply any Funds with properties. not altering calculator via proofs.
variable (Z': ((Labels.frames G).level d).Coeff→ Coefficient ((Labels.frames G).level d) (H.S.side (m+1) n))
variable (hs:Funds (m:=m+1) κ (hol G) p l (localSection G d) (H.rep N n (m+1)) V Z' (Real.sqrt (H.levels.clock.forcedAllowance (m+1))) r ν)
local notation "CP"=> parcelP H N n φB m V K U T
local notation "F0" i=> (V.plays (V.index.symm (Size.axis F i)))
include hP ha ht hq hb hs hV
lemma marl (i:(F).Index): Circuit Y L d κ p l 0 0 v' ((F0 i).exponentialEntry 0 B' R1) (profile (R1).activities (F0 i).forced) (profile (R0).activities (CP i|>.forced)) ((Size.axis F i) 0) feeE gnE baseq:=by
    let X:= V.index.symm (Size.axis F i); let D:= V.plays X; have hv:V.index X= Size.axis F i:= V.index.apply_symm_apply _; have hZ:=(Ticket.opportunities B' φB V hs)
    let D' := Z' X; let Q:= rack K D; let U₁ := T.fullP i
    let t:= V.charge X; let P':= (R1)
    have hL : (F).coeffSize (V.index X)=1:=by rw [hv,Size.size_axis]
    have he:Exhibition B' κ l p φB P' D D' (κZ) ν r:= by
       have he:= hs X; change Exhibition _ _ _ _ _ _ _ _ _ (ν*_) (r*_) at he; rw [hL,mul_one,mul_one] at he; exact he
    have hr:t ≤ x0:= calc
        _ ≤ _:= hb.cone X
        _ ≤ (H.levels.params (m+1)).columns*(F).coeffSize (V.index X):= mul_le_mul_of_nonneg_left (Work.G08.size_core F _) (zero_le_one.trans (H.levels.params (m+1)).columns_ge)
        _ = _:=by rw [hL,mul_one]
    let J' := hZ.some i; have hp := U₁.front
    have hK':0≤ U₁.k:= nonneg_of_mul_nonneg_right (sumBudget_credit U₁.pier) (Real.sqrt_pos.mpr (Extra.Histories.forcedPos ..))
    have hh : (Vinca.decrement D D').forced=D.forced:= by change D.forced-D'.forced=D.forced;rw [he.stock.forced,sub_zero];
    have ht' : (rack K (Vinca.decrement D D')).forced= Q.forced:=by unfold Q rack stowK; rw [hh]
    apply XPre.sanctioned d K U A D (T.fullP i) D' hD i ((hb.currents X).trans hv) ha ht hq J' he.layout (he.fee.regular) ?_ ((hb.earns X).2) hP ⟨hp.1,hp.2.1,hp.2.2.trans ((le_add_of_nonneg_right hK').trans (U₁.uniont.trans hr))⟩ hV
    obtain ⟨L,b,hv',_,hx,_,H₁,q,hq,hQ⟩:= MergeProof.keeps K _ (he.fee.bound le_rfl); rw [← ht']; exact ⟨q,⟨hq.1,hq.2.1,hq.2.2.trans (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_left hv').trans hx) (Real.sqrt_nonneg _))⟩,hQ⟩
end YM.LocalLTE.XPre
