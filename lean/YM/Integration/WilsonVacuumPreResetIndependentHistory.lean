import YM.Integration.WilsonVacuumPreResetCanonicalCoil
import YM.Integration.WilsonConditionalTaylorWheelRawColor
import YM.Integration.WilsonConditionalTaylorWheelClock

/-! Identify the cover vacuum and its kinetic coordinate along one actual finite history. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetIndependentHistory
open Function Filter Lattice Laurent RG Wilson Exterior Precision Tree Bloch Next.Foundations PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos PhysicalNext.Repeat.Legato
open Next.Free FormalBulk08 Flat Reef Orb Series Jets Shore Lava Wine Roof Lotus Mesa
open scoped Classical Topology BigOperators

variable {G:Gauge} (R:Run G) (u:G.ColorIndex)
local notation "V" => R.family.path.levels
set_option quotPrecheck false in
local notation "wood" => (fun k:ℕ=>Flat.routes (R.family.path.levels.clock.op k 0).patch)
set_option quotPrecheck false in
local notation "b" => (fun k:ℕ=>(R.family.path.levels.blocks k 0).branches)

def Filed (N j:ℕ):Prop:=
  ∀e r:ℕ,-actionW V R.metals.O N j e (r+1)=Dove.model V wood b R.metals.O u N j e (r+1)

def Pre (N j:ℕ):Prop:=
  let W:=Dove.model V wood b R.metals.O u N (j+1)
  let raw:=FormalBulk08.Bank.waken (destination V N j) (wood j) W R.metals.O (b j)
  (∀e r:ℕ,-freshet V R.metals.O N j e (r+1)=raw e (r+1)) ∧
    pitch V R.metals.O N j=Wine.scalar u raw

private theorem cork (u:G.ColorIndex) (X:Cork.Slopes G):Cork.value u (-X) = -Cork.value u X:=by
  simp only [Cork.value,Cork.mir,Cork.net,Cork.hem,Pi.neg_apply,neg_mul,tsum_neg]

theorem step (simple:G.Simple) {c:ℕ} (Q:Realm G (c+1) Credit.leanC)
    (levels:Q.draws=R.family.path.levels) (scheme:Q.paid=R.metals.O)
    (tags:∀i n,(primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (N j:ℕ) (live:j<N) (old:Filed R u N (j+1)):Pre R u N j ∧ Filed R u N j:=by
  let W:=Dove.model V wood b R.metals.O u N (j+1)
  let raw:=FormalBulk08.Bank.waken (destination V N j) (wood j) W R.metals.O (b j)
  have rows (e r:ℕ): -freshet V R.metals.O N j e (r+1)=raw e (r+1):=by
    cases e with
    | zero=>exact WilsonVacuumPreResetIndependentCoil.classical R simple u N j (tags j) live r
    | succ k=>
      exact WilsonVacuumPreResetCanonicalCoil.original R simple u N j live (k+1) (k+1) r
        (Nat.succ_pos k) le_rfl (fun d _ a _=>old d a) (tags j)
  have kinetic:pitch V R.metals.O N j=Wine.scalar u raw:=by
    ext e
    have h:=WilsonConditionalTaylorWheelRawColor.original Q N j live e u
    rw [levels,scheme] at h
    rw [h,Wine.scalar,coeff_mk,←rows e 1,cork]
  refine ⟨⟨rows,kinetic⟩,?_⟩
  have pub:=WilsonConditionalTaylorWheelClock.onRealm Q N j live
  rw [levels,scheme] at pub
  intro e r
  rw [conduct V R.metals.O live,pub.2.2,Dove.through V wood b R.metals.O u N j live]
  change -Wine.stamp _ _ (lop (freshet V R.metals.O N j)) e (r+1)=
    Wine.stamp (Wine.bookH (Wine.scalar u raw)) (Wine.bookU (Wine.scalar u raw)) raw e (r+1)
  rw [kinetic,Wine.stamp,Wine.stamp,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [←smul_neg]
  simp only [lop,if_neg (Nat.succ_ne_zero r),rows i r]

/-- One selector and one funded original course work at every finite cutoff and angular order. -/
theorem original (simple:G.Simple) (v:ℕ→Gear G→ℝ) (funded:FundedMarkedCoverRows.prices v R.kit)
    (tags:∀i n,(primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (N j:ℕ) (date:j≤N):Filed R u N j ∧ (j<N→Pre R u N j):=by
  have fundedRealm:=FundedMarkedCoverRows.realm R simple v funded 0 (fun _=>0) (fun _=>1)
    (fun _=>Nat.zero_lt_succ _) 0 0 0
  obtain ⟨_,Q,levels,scheme,_⟩:=fundedRealm.exists
  induction date using Nat.decreasingInduction with
  | self=>exact ⟨fun e r=>WilsonVacuumPreResetIndependentBirth.original R simple u wood N e r,fun h=>False.elim (lt_irrefl _ h)⟩
  | of_succ k live prev=>
    have next:=step R u simple Q levels scheme tags N k live prev.1
    exact ⟨next.2,fun _=>next.1⟩
end YM.Integration.WilsonVacuumPreResetIndependentHistory
end
