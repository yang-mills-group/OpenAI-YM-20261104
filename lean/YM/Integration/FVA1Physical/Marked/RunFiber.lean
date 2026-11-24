import YM.GapsR2RG.FiberPay
import YM.LocalLTE.Concourse.Memo

/-! Transport newly inserted scalar fields at any anchor on the actual purchased
run. The constant is passed through the same positive vacuum, separately from
the countable regular and forced support invoice. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Function Filter Finset MeasureTheory Lattice RG YM.Wilson Source Labels Extra.Histories
open Next.Foundations Push.Local LocalLTE.Concourse LocalLTE.Vinca PhysicalNext.Repeat.Legato GapsR2RG
open scoped Classical BigOperators
variable {G:Gauge} (hG:G.Simple) (R:Run G) {N n m:ℕ} (hm:m < N) (start:R.t 0 ≤ m)
local notation "H" => R.family.path
local notation "RI" => (H).rep N n (m+1)
local notation "RO" => (H).rep N n m
local notation "K" => (H).levels.clock.op m n
local notation "F0" => (frames G).level 0
local notation "D0" => localSection G 0

include hG hm start
theorem run_full_fiber (y:Site (R.family.side (m+1) n))
    (P:Coefficient F0 (R.family.side (m+1) n)) {c:ℝ}
    (form:P.Format y (hol G) RI) (invoice:P.remBound y RI (kappa H (m+1)) c) :
    let z:=(K).ratio.parent y
    let r:=Doors.rate ((H).S.block m)*c
    ∃ Q:Coefficient F0 (R.family.side m n), Q.Format z (hol G) RO ∧
      Q.density z D0 RO=(K).push (RI).beta (P.density y D0 RI) ∧
      Q.remBound z RO (kappa H m) r ∧ (F0).coeffSize (Q.x-P.x) ≤ r := by
  intro z r
  let Z:=memo 0 P
  obtain ⟨U,format,dens,cost,bound⟩:=Anchor.displacedFiber hG R hm start y Z rfl c
    (memo_format 0 form) (memo_cost 0 invoice)
  let V:=memo (U.x+P.x) U
  refine ⟨V,memo_format _ format,?_,memo_cost _ cost,?_⟩
  · have split : P.density y D0 RI=Z.density y D0 RI+(P.x 0) • liftVac H N n (m+1) := by
      funext Y
      have h:=memo_density P.x Z D0 y RI Y
      simpa [Z,memo,Pi.add_apply,Pi.smul_apply,liftVac] using h
    have integrable:=play_integrable H N (B:=D0) R.makes.wilson hm (memo_format 0 form) (memo_cost 0 invoice)
    have vacuum:=vac_integrable H N n (m+1) R.makes.wilson hm
    have recur : liftVac H N n m=(K).push (RI).beta (liftVac H N n (m+1)) :=by
      simpa [blast] using (blast_vac H N n m 0 R.makes.wilson hm).symm
    funext Y
    rw [show V.density z D0 RO Y=_ from memo_density (U.x+P.x) U D0 z RO Y,
      dens, split, StepData.push_add ((H).levels.transition_mass m n _) _ _ integrable
        (vacuum.smul (P.x 0)), StepData.push_smul _ _ _ _ vacuum, ←recur]
    simp only [blast,pow_zero,one_mul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,liftVac,add_sub_cancel_left]
    rfl
  · change (F0).coeffSize (U.x+P.x-P.x) ≤ r
    rwa [add_sub_cancel_right]
end YM.Integration.FVA1Physical.Marked
