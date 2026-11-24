import YM.OPE.Samples.Musical
import YM.OPE.Trunk.Beacon
/-!
# Fund at a whole forecast
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk.Payments
open Function Filter Finset Lattice RG Wilson Source Extra.Histories Labels Pressure
open Push Marker Local MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open Book Book.Mask PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid
open Drapery Backup Motion Extra.Multi Next.Rank.Station Cells
open Book.Tariff Playout.Rake Rhythm.Store Rhythm
open scoped Topology BigOperators Classical ContDiff
variable {I J Z : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J] {G:Gauge}
    {H l m k b N p A t t' q d:ℕ}{Q: Rhythm I}{C:Family G}
set_option quotPrecheck false
variable {Y:Type}{f:Filter Y}{T a c : Y→ℝ}{R r:Y→ℕ→ℝ}{α:ℕ→ℝ}{P:ℝ}
    {F:Y→Loom Q} {B:Border f T Q.limit R r α} (D:Oscars B P F C)
variable {W r' D'}(L:LogPackage C W r' D')
local notation "Y!"=> C.path.levels
local notation "b!"=> (fun i t=> (F i).below t)
local notation "j!"=> (fun i t=> (F i).launch t)
local notation "β"=> C.path.levels.clock.hatBeta
local notation "μ!"=> C.S.a
local notation "τ!"=> ValueStamp f T
include D
lemma tip (h:t≤ Q.limit) : τ! (fun i=> μ! (j! i t)/R i t):= by
    apply ((D.toll t h).div (B.relative t h)).congr; filter_upwards [(B.rates t h).pos,(B.ahead h).pos] with i hi he; field_simp
include L
lemma peer_stamp (he:0<A)(h:t ≤ Q.limit): τ! (fun i=>peer L A (j! i t)):= by have hm:= D.upper t h; exact (((nearStamp B.life hm).mul (lamina_stamp L B.life he hm)).div (ValueStamp.const B.life (by norm_num : (0:ℝ)<8))) -- order
lemma shelfstamp (h:t ≤ Q.limit) : τ! (fun i=>shelf C (b! i t)):=by
    have hT:= B.life; have hx:= D.lower t h; let φ i:= shelf C (b! i t); have hφ i:1 ≤ φ i:= shelf_purchase
    refine ⟨Eventually.of_forall fun i=> zero_lt_one.trans_le (hφ i),((((Wallet.const hT (4:ℝ)).mul ((Wallet.const hT _).add hT (columnsWallet L hT hx)))).mul ((betaStamp hT (hx.step (Y!).fits.mesh)).up)), (ValueStamp.const hT one_pos).down.invLe (Eventually.of_forall fun _=> one_pos) (Eventually.of_forall hφ)⟩
lemma chary_stamp (h:t ≤ Q.limit)(d:ℕ) : τ! (fun i=>chary C (b! i t) d):= (flyStamp B.life (D.lower t h) d).div ((ValueStamp.const B.life (by norm_num:(0:ℝ)<8)).mul (shelfstamp D L h))
lemma costBand (h:t ≤ Q.limit): τ! (fun i=> μ! (j! i t)/ μ! (b! i t+1)):=by
    apply (((tip D h).div (D.loggap t h)).mul (blockWallet L B.life (D.lower t h))).congr; filter_upwards [(B.ahead h).pos] with i hi; rw [Schedule.a_step]; let v:= (F i).below t; have hp:0 < ((C.path.S.block v).val:ℝ):=(by exact_mod_cast (C.path.S.block v).property); let y:= μ! (b! i t); have hh:0<y:= C.S.a_pos _
    field_simp -- push casts
variable {x:Y→ℕ→ℝ}
include D L
lemma proceeds (h:t ≤ Q.limit) (hc:0<A)(hx:ValueStamp f T (fun i=> x i (t+1))): τ! (fun i=> provision L (F i) A (x i) t):=by -- cell formula
    have hh := peer_stamp D L hc h; have hp:= B.life; exact ((((costBand D L h).pow hp 4).mul (hh.pow hp _)).mul hx).pow hp _
lemma onward (h:t ≤ Q.limit)(hc:0 < A)(hx:ValueStamp f T (fun i=> x i (t+1))) : τ! (fun i=> transact L (F i) A (x i) t):=by
    have hp:= proceeds D L h hc hx; have hT:= B.life; have hu:= D.lower t h; exact ((((renalStamp hT hu).mul (nearStamp hT hu)).mul (hp.div ((ValueStamp.const hT (by norm_num: (0:ℝ)<4)).mul (betaStamp hT (hu.step (Y!).fits.mesh))))).mul (chary_stamp D L h 0))
lemma recipient_price (h:t ≤ Q.limit)(hc:0 < A)(hx:ValueStamp f T (fun i=> x i (t+1)))(d:ℕ) : τ! (fun i=> discharged L (F i) A (x i) t d):= ((onward D L h hc hx).mul (proceeds D L h hc hx)).mul (chary_stamp D L h d)
-- At a fixed degree, one family of wages satisfies the rates and the value estimates through Q.limit + 1.
lemma regWage (hG:G.Simple) (hp:0<A)(d:ℕ): ∃ x:Y→ℕ→ℝ,(∀ t,t ≤ Q.limit+1 → τ! (fun i=> x i t))∧ ∀ i, Rates (F i) L A {d} (x i):=by
    let v:=Q.limit+1; let g (i:Y)(u:ℝ)(t:ℕ):= discharged L (F i) A (fun _=>u) t d
    let X (i:Y):ℕ→ℝ:= fun n=> Nat.rec (motive:=fun _=>ℝ) 1 (fun l y=> g i y (v-(l+1))) n; let x (i:Y)(t:ℕ):= X i (v-t)
    have ht(i:Y): x i v=1:=by unfold x; rw [tsub_self]; rfl
    have he(i:Y)(t:ℕ)(h:t < v): x i t=discharged L (F i) A (x i) t d:=by
        let y:= v-(t+1); have hp:y+1=v-t:=(by unfold y; omega); have hh: X i (v-t)=X i (y+1):= congr_arg _ hp.symm; rw [show x i t= X i (y+1) from hh,show X i (y+1)= g i (X i y) (v-(y+1)) from rfl, show v-(y+1)=t from (by omega)]
    have hK(i:Y)(t:ℕ)(h:t ≤ v): Cash (x i t):=by
       induction h using Nat.decreasingInduction with
       | self=> rw [ht]; exact Cash.one
       | of_succ t h IH=> rw [he i _ h]; have hp' := Q.belowLaunch (F i) (show t ≤ Q.limit from Nat.le_of_lt_succ h); exact Tariff.erase_cash ((Tariff.checkOut (W:=W) L hG hp IH hp').2.2.1) ((Tariff.amounts L hG hp IH hp').1)|>.1
    refine ⟨x,fun t h=> ?_, fun i=>⟨fun t h=> hK i t h, fun t h=>?_,fun t d' h ht'=>?_⟩⟩
    · change t ≤ v at h; induction h using Nat.decreasingInduction with
      | self=> exact (ValueStamp.const B.life one_pos).congr (Eventually.of_forall fun i=>(ht i).symm)
      | of_succ t h IH=> exact (recipient_price D L (show t ≤ Q.limit from Nat.le_of_lt_succ h) hp IH d).congr (Eventually.of_forall fun i=>(he i t h).symm)
    · have hh:= he i t (Nat.lt_succ_of_le h); have hU:= Q.belowLaunch (F i) h; have hV:= hK i (t+1) (Nat.succ_le_succ h); exact hh.trans_le (Tariff.erase_cash (Tariff.checkOut L hG hp hV hU|>.2.2.1) (Tariff.amounts L hG hp hV hU|>.1)|>.2)
    exact (mem_singleton.mp ht').symm ▸ (he i t (Nat.lt_succ_of_le h)).le
end YM.OPE.Log.Trunk.Payments
