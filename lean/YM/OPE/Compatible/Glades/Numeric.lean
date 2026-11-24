import YM.OPE.Compatible.Glades.Rebate
/-!
# Complete paid outcome for one array, still posed on lattice. Actual proof below sends the physical exterior through panels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.CutOrder
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float Next.Rank Station Next.Rank.Spindle
open Push Marker Local Extra.Histories Extra.Trajectories MeasureTheory Extra.Multi Finset Cells
open Ribbon
open scoped Topology Classical
variable {X:Type}[PartialOrder X][OrderBot X]
open YM.OPE.Allot Series Lights
variable {G:Gauge}{C:Family G} (A:Allot C){N p J k j d b:ℕ}{a:ℝ}(hN:j<N)(hv:Stock.Tabs.opens C.path.levels 1 J k)(hk:k ≤ j)
variable (g:Config G (C.side N p)→ℂ)
set_option quotPrecheck false
local notation "COPY" => Site (C.side J p)
local notation "E"=> Mix.camp C p J
local notation "T"=> center C.S p (hv.1.trans (hk.trans hN.le)) 0
-- fixed Ensemble if directly using Windfall on rooted copy pattern. or any P.Move.
def listP (C:Family G)(p J:ℕ) : Ensemble (Site (C.side J p)):=
   ⟨0,hands C p J,fun i=>Equiv.swap 0 i,fun _=>Equiv.swap_apply_left ..,P_on ..⟩
lemma draw (hP:C.ref d ≤ k)(hp:C.ref 0 ≤ j)(hG:G.Simple)(h:C.Makes)(hq:GridApprox.room C.path.levels J j (lensScope C d))(ha:0<a)(hc:Continuous g)
   (hf:∀ t:C.label d,Interior ((T).chamber 0) (C.O N p t 0))(he:Interior ((T).chamber 0) g)
   (hh:Head ({⊥}:Finset X) A (listP C p J) (j+1) N p b E E (fun i=>(T).copy i g) a hN):
   ∃ z:C.label d, Next.UVStress.quota C d j N p z ≤ 2*(owed C a d j) ∧ Interior ((T).chamber 0) (g-C.O N p z 0)∧ (T).rootTest (C.beta N p) (g-C.O N p z 0) ≤ 2*(stakes C J k/rebate C a d k j):=by
   let H:= C.path; let y:=β C (j+1); let w:= badge_fee C a j; let r:=rebate C a d k j; let μ:= near C.path.levels
   let u:=(march (fun _:Unit=>r) μ k j) (); let W:=march (fun _:Site (C.side J p)=>r) μ k j
   have hr : 0<r:= rebate_positive ha A hP hk; have hw:0<w:= badge_pos ha; have hu:w ≤ a:= div_le_self ha.le (by have h:1 ≤ β C (j+1):=(β_one ..).le; linarith only [h])
   have hQ : 0 ≤ 4*(1/a):=by positivity
   have hY:4*w*(4*(1/a))≤1:=by
      have h:1≤y:= (β_one ..).le; change 4*(a/(16*y))*(4*(1/a))≤_; field_simp; linarith only [h]
   have hπ:w*(y*(4*(1/a)))≤1:=by
      have he:0<y:=β_pos ..; unfold w badge_fee; change (a/(16*y))*(y*(4*(1/a)))≤_; field_simp; nlinarith only [he,ha]
   let Q:=center C.S p (hv.1.trans (hk.trans hN.le)) 0; have hz(i:ℕ)(he:J≤ i):Injective ((Mix.camp C p J) i):=by rw [show Mix.camp C p J i= _ from funext (elev C J p i he)]; exact (C.S.toDepth he p).embed_injective
   have hm: Migrating H j p (j+1) (Mix.camp C p J) := uphill C J j p (j+1) (hv.1.trans hk)
   let δ:=renal C.path.levels; have hB : Brine C.path k δ μ:=⟨fun i _=> A.buy.system.costs.stay.water _ (Nat.zero_le i),fun i _=>A.buy.system.costs.stay.mint _ (Nat.zero_le i),fun i _=>A.buy.system.costs.stay.split _ (Nat.zero_le i),fun i _=>A.buy.system.costs.stay.support _ (Nat.zero_le i)⟩
   have hU : 0<u:=march_pos _ _ _ _ _ (fun _=>hr) hB j hk _
   have hR:=setting_value ha A hP hk hG
   obtain ⟨F,hF,hZ,hM,hT⟩:= badge A (V:=Site (C.side J p)) (fun i=>Q.copy i g) (hP.trans hk) hp h hN ha hh (fun i=> cappedC C J p N _ (fun _=>g) (i,false) hc) hm hm (hz _ (hv.1.trans hk)) (hz _ ((hv.1.trans hk).trans j.le_succ)) hw hu hY hπ hU hR.1
   let q:=C.S.a (j+1)^d*(y*(4*(1/a))); have hq':0<q:=mul_pos (pow_pos (C.S.a_pos _) _) (mul_pos (β_pos ..) (by positivity))
   have hu:∀ i:ℕ, ∀ t:COPY,(march (fun _:COPY=>r) μ k i) t= (march (fun _:Unit=>r) μ k i) ():=by
       intro i t; induction i with
       | zero=>rfl
       | succ m ih=> by_cases he:k ≤ m <;> simp [march,he,ih]
   rw [← show W=(fun _=> u) from funext (hu j)] at hT
   obtain ⟨z,ha,hb⟩:= bequeathed C N j k p d h r A.buy.system A.buy.tabs J hv g F hP (hk:=hk) hN hq hf hc he hZ hM ((add_le_add_left hF q).trans (show _ ≤2*q from le_of_eq (by change q+q=2*q; ring))) (mul_pos zero_lt_two hq') (le_refl _) hr hR.2 hT
   exact ⟨z,ha,Next.UVStress.minus he (hf _),hb⟩
end YM.OPE.Arboreal.CutOrder
