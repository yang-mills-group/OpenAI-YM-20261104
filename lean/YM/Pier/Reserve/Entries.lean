import YM.Pier.Reserve.Corridor
/-!
# Hand the price to the actual column Reader contract

For any terminal-based coordinate, the FULL `density` defect is supplied in
supported column norm after exact Keeper capture. No healthy configuration
restriction to evaluate the equality of densities; `Tab/Room` as usual use
masked regular germs on their proper domains, pay full support, keep forced
divisor. Do not change to pert. basis. We measure units and reserve of the
SINGLEMARK channels, not price a difference of books of multiple marks.
No implication to `matrixTicket` is justified merely from this approximation.
Charge explicit includes the usual mark-scale factors. In particular the corridor
output B is an **edited numerical stock**, not one known by independent
calculation in terms of Wilson perturbative coefficients.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Pier.Mooring
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Mallow Lotus Legato Legato.Campaign Legato.Bandage
open YM.MergeProof Matric Matric.Gram
open Pressure ConnectedActivityE6 Blaze March Lim Umbra FullVolume.Paint
open Guard RG.Shoot Lark Rain Blush Motion Boutique
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} (R:Run G) {T:Legato.Campaign R} (W:Pillars R T)
variable (d:ℕ) {j p N:ℕ}
local notation "H" => R.family.path
local notation "Z" => R.family.path.rep N p j
local notation "hk" => R.tuning.receipts
local notation "B" => (R.stories d N p)
local notation "b" => R.family
local notation "κ" => Real.sqrt (R.family.path.levels.clock.forcedAllowance j)
variable (hr:R.t d ≤ j)(hj:j≤N)

section
local notation "Y" => (books R W N p d j)
include hr
lemma occupancy_books (x : ((Labels.frames G).level d).Coeff) :
    Coin.uses ((Y).g ((B).entries j x).x) = capture ((B).entries j x)
      (Keeper.sufficient ((W.yields N p).slots j (Nat.zero_le _) hj)) := by
  exact (W.yields N p).capitals R.b (fun i=> brochure R.T i p R.tuning.receipts) (Nat.zero_le _) (R.accepts d)
    (R.stories d N p) (fun he=> W.ports d N p he) j hr hj x

-- accounting at all levels including top. threshold convention follows R.family.Schedule
include W hr hj
set_option maxHeartbeats 500000 in
theorem consumesWithin (z : ((Labels.frames G).level d).Coeff) (U:Grid R j p d) (x:ℝ)
    (he:Within (books R W N p d j) U x) :
    let V₀:= (R.stories d N p|>.entries j z)
    let V:= book V₀.x (Coin.uses ((books R W N p d j).g V₀.x))
    let V':= book V₀.x (Coin.uses (U.g V₀.x))
    let P:=breakP V V'
    let L:= R.family.path.rep N p j
    P.Format 0 (hol G) L ∧ P.remBound 0 L κ (x*(R.family.path.levels.params j).columns*((Labels.frames G).level d).coeffSize V₀.x) ∧
      V.Format 0 (hol G) L ∧ V'.Format 0 (hol G) L ∧
      V.exponentialEntry 0 (localSection G d) L=V₀.exponentialEntry 0 (localSection G d) L ∧
      profile L.activities V.forced=profile L.activities V₀.forced ∧
      P.x=0 ∧
      P.density 0 (localSection G d) L= (show Config G (R.family.side j p)→ℂ from V₀.density 0 (localSection G d) L)-(show Config G (R.family.side j p)→ℂ from V'.density 0 (localSection G d) L) := by
   intro A0 V V' P L
   let K:= Keeper.sufficient ((W.yields N p).slots j (Nat.zero_le _) hj); let q:= A0.x
   let U₀:= (Y).g q; let U₁:= U.g q
   have hv: Coin.uses U₀=capture A0 K:= occupancy_books R W d hr hj z
   have hy: V= book q (capture A0 K):= congr_arg (Matric.book q) hv
   have ht:= R.makes.calibrated d N p (hr.trans hj)
   have hF : A0.Format 0 (hol G) L:= ht.format j hr hj _
   have hw:Well L (attire R.T j p) κ:= (W.yields N p).notices (fun i=> brochure R.T i p R.tuning.receipts) (Nat.zero_le _) hj
   obtain ⟨hfp,hBp⟩ := granted hw (hol G) q U₀
   obtain ⟨hBq,hpq⟩ := granted hw (hol G) q U₁
   have hV:P= (book (q-q) (Coin.uses (U₀-U₁))):=by rw [map_sub]; rfl
   obtain ⟨hT,hQ⟩:= granted hw (hol G) (q-q) (U₀-U₁)
   have hp: V.density 0 (localSection G d) L= A0.density 0 (localSection G d) L:=by rw [hy]; exact pays A0 K (localSection G d) hF (ht.cap j hr hj _) (R.makes.wilson.represents N p j hj).good
   have h' : P.remBound 0 L κ (x*(R.family.path.levels.params j).columns*((Labels.frames G).level d).coeffSize A0.x):=hV.symm ▸ rem_mono hQ (he.2 q)
   refine ⟨hV.symm ▸ hT,h',hfp,hBq,hy.symm ▸ expo A0 K (localSection G d) hF,hy.symm ▸ profited A0 K,?_,?_⟩
   · rw [hV,book_x,sub_self]
   rw [← hp]; exact Pier.Slate.density_difference (R.makes.wilson.represents N p j hj).good hBp hpq h' rfl
end

end YM.Pier.Mooring
