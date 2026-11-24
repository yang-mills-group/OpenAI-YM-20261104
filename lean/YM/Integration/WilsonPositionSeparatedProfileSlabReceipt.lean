import YM.Integration.WilsonReportHarvestSlabReceipt
import YM.Integration.WilsonPositionSeparatedProfileSlabPhysical

/-! The charged receipt for a submitted rank-one test pays its entire signed
original scalar, uniformly over all earlier cuts of this same physical course. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileSlabReceipt
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi Push.GridApprox
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station Ribbons
open WilsonReportHarvestSlabLabels WilsonAllDateHarvestPropagation
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G:Gauge} (R:Run G)
set_option quotPrecheck false
local notation "C" => R.family

theorem original (book:OPE.Package (C) R.w (mutt (C).path.levels R.Q) R.doors)
    {b a t N per:ℕ} (na:b+1 ≤ a) (aturn:a ≤ t) (nt:b+1 < t) (top:t ≤ N)
    (s:Fin 3→ℕ) (S:(i:Fin 3)→Emblems C (s i)) (P:(i:Fin 3)→Sight C (s i) per)
    (x:(i:Fin 3)→Palette C (s i)) (o:Fin 3→Site ((C).side (b+1) per)) (E:Fin 3→Motion)
    (q:ManyStem C o (b+1)→Body) (target:ℝ)
    (issued:WilsonReportHarvestSlabReceipt.Captured R na aturn nt top s S P x o E q target):
    let n:=b+1
    let roster:=Stock.census (Fin 3)
    let A:=Mine.tree o E
    let J:=Mine.ward o E roster
    let Y:=(C).path.rep N per
    let rows:=imprint R.makes A (headings o E q) (plants (m:=a) s P S x) t top
    let color:=WilsonAllDateHarvestPhysical.columns o E s q S x a N n
    let real:=gust (C).path N per N (birth (J n) (Y N) color) n (nt.le.trans top)
    let gate:=WilsonAllDateHarvestEndpointOpening.opening
      (WilsonMixedTaggedSeparatedBoard.admitted o E roster na aturn) (shadow A s (headings o E q) t)
    let inlet:=fun W=>gate (density (Y t) rows (fun _ _=>0) (fun _ _=>0) W)
    ∃ L:∀j,Config G ((C).side j per)→Poly (J j),∃route:Replay A s (le_refl n) t L N,
      L t=inlet ∧
      (∀j (nj:n ≤ j) (jt:j ≤ t) V, ((Y j).eval V)⁻¹ • L j V=
        actualTransport C (N:=N) (fun W=>((Y t).eval W)⁻¹ •
          WilsonReportHarvestEarlierSlab.route route j nj jt (inlet W)) jt V) ∧
      ∀u, (C).ref 0 ≤ u → ∀age:u ≤ b,
        ‖pushTo (C).path N per (age.trans b.le_succ)
            (fun W=>(baseFold o E roster (real W)).part entire-(baseFold o E roster (L n W)).part entire)
            1/liftVac (C).path N per u 1‖ ≤ (1+WilsonPositionSeparatedProfileStableReturn.price)*target := by
  intro n roster A J Y rows color real gate inlet
  obtain ⟨L,route,first,carried,cost,X,form,cash,unit,paid,seen⟩:=issued
  refine ⟨L,route,first,carried,?_⟩
  intro u grade age
  rw [←seen u age]
  have bound:=WilsonPositionSeparatedProfileStableReturn.original R book grade age
    (b.le_succ.trans (nt.le.trans top)) X form cash
  have entry:‖X.x 0‖≤((C).labels.level 0).coeffSize X.x:=
    Finset.single_le_sum (fun _ _=>norm_nonneg _) (Finset.mem_univ _)
  have nonneg:0≤WilsonPositionSeparatedProfileStableReturn.price:=
    div_nonneg WilsonPositionSeparatedProfileStableStep.shrink_pos.le (sub_pos.mpr WilsonPositionSeparatedProfileStableStep.shrink_lt).le
  calc
    _ ≤ ‖WilsonPositionSeparatedProfileStableReturn.read (N:=N) R age X-X.x 0‖+‖X.x 0‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ WilsonPositionSeparatedProfileStableReturn.price*cost+cost := add_le_add bound (entry.trans unit)
    _ = (1+WilsonPositionSeparatedProfileStableReturn.price)*cost := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left paid (by linarith)

end YM.Integration.WilsonPositionSeparatedProfileSlabReceipt
