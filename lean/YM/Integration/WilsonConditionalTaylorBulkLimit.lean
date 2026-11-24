import YM.Integration.WilsonConditionalTaylorCourseLedger
import YM.Integration.WilsonConditionalTaylorBulkStamp
import YM.Integration.WilsonKineticSpatialClock

/-! Finite period to infinite volume matching at every height and perturbative
order, after every nonlinear integral and every physical coupling reset. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorBulkLimit
open Filter PowerSeries Lattice RG Wilson Tree Stationary Push.Uniform Bloch
open FormalBulk08 Jets Flat Reef Mesa Lava Shore Lotus Wine Bank Orb Cork Next.Free
open PhysicalNext.Repeat.Legato WilsonConditionalTaylorBulkShape WilsonConditionalTaylorBulkHistory
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) (simple : G.Simple) (u : G.ColorIndex)
variable (wood : ∀ j,Lodge (R.family.path.levels.clock.op j 0).patch)
variable (tags : ∀ j n, (primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)

include simple in
theorem full (N j : ℕ) (paid : j≤N) : ∀ e r,0<r →
    ∃ η:ℝ, 0<η ∧ Kith η
      (Dove.model R.family.path.levels wood (fun i=>(R.family.path.levels.blocks i 0).branches) R.metals.O u N j e r)
      (fun n=>rancho (course R u wood tags N j n) e r) :=by
  let V:=R.family.path.levels
  let K:=RunFormalChain.fromRun R
  let b:=fun i=>(V.blocks i 0).branches
  induction paid using Nat.decreasingInduction with
  | self =>
    intro e r live
    let i:Fin r:=⟨0,live⟩
    have Y:=Dove.genu V wood b R.metals.O u K.receipt simple (N:=N) (i:=N) le_rfl
    rw [Dove.leaves] at Y
    rw [Dove.leaves]
    obtain ⟨s,C,hs,expense⟩:=Y.fare e r
    refine ⟨s,hs,?_⟩
    simp_rw [ultraviolet R u wood tags N,Mesa.bend e i]
    exact stable hs.le (Y.civil e r) expense i
  | of_succ j hi ih =>
    let P:=destination V N j
    let W:=Dove.model V wood b R.metals.O u N (j+1)
    let U:=course R u wood tags N (j+1)
    let Z:=raw R wood tags N j U
    let T:=waken P (wood j) W R.metals.O (b j)
    have old:=Dove.genu V wood b R.metals.O u K.receipt simple (N:=N) (i:=j+1) hi
    have every (e r : ℕ) (pos : 0<r) : ∃ s:ℝ, 0<s ∧ Kith s (T e r) (fun n=>rancho (Z n) e r):=by
      apply WilsonConditionalTaylorBulkPass.full P (wood j) W R.metals.O (b j) (tags j) U old.toVivid K.receipt
        (V.clock.adm j) e r (⟨0,pos⟩ : Fin r)
      · exact fun n=>(admitted R u wood tags N (j+1) hi n).1
      · exact fun n=>(admitted R u wood tags N (j+1) hi n).2.1
      · exact fun a _ d hd _=>ih a d hd
    have story:=Bank.creed P (wood j) W R.metals.O (b j) old.toStory (V.clock.adm j) K.receipt
    have base : Fresh (Wine.scalar u T):=by
      change coeff 0 (mk (fun e=>Cork.value u (T e 2)))=1
      rw [coeff_mk,show T 0 2=_ from story.ink,Cork.pink_weigh _ V.clock.kernel.penalty_pos (V.clock.adm j)]
    have civic : ∀ᶠ n in atTop,Civic (Z n) :=.of_forall (fun n=>(WilsonConditionalTaylorCourseLedger.rawField R u wood tags N j hi n).2.2)
    let H:=WilsonKineticSpatialClock.finite R u N j Z
    let C:=Wine.scalar u T
    have bank (e:ℕ):=WilsonKineticSpatialClock.full R u N j Z simple wood T e hi.le civic base
      (fun a _ _=>every a 2 (by decide)) e le_rfl
    intro e r positive
    rw [Dove.through _ _ _ _ _ _ _ hi,next R u wood tags N j hi]
    exact WilsonConditionalTaylorBulkStamp.action T Z (A:=bookH C) (B:=bookU C)
      (a:=fun n=>bookH (H n)) (b:=fun n=>bookU (H n))
      (fun q=>(bank q).2.1) (fun q=>(bank q).2.2) e r (fun q _=>every q r positive)

end YM.Integration.WilsonConditionalTaylorBulkLimit

