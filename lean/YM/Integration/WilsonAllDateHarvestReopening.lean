import YM.Integration.WilsonAllDateHarvestHistoricalEntry
import YM.Integration.WilsonAllDateHarvestTuningModes

/-! The old list and the list admitted anew at an eligible upper date give
the same opened vacuum-with-singletons. All signed old partners are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestReopening

open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open WilsonAllDateHarvestAffine WilsonAllDateHarvestPropagation WilsonAllDateHarvestStability
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical


open WilsonAllDateHarvestEndpointOpening WilsonAllDateHarvestLedger
open private sheltered from YM.Integration.WilsonAllDateHarvestTuningModes

theorem tempered {V:Type} [DecidableEq V] {B J:Census V} (inc:B.choices⊆J.choices) (D:Set V)
    (gate:∀i:J.Mode,i.val∉B.choices → ¬Disjoint D (i.val:Set V)) (x:Poly J):
    opening inc D (narrow inc x)=temperV J D x := by
  ext i
  change (wrap B J (temperV B D (narrow inc x))).part i=(temperV J D x).part i
  by_cases member:i.val∈B.choices
  · let z:B.Mode:=⟨i.val,member⟩
    rw [show i=route inc z from rfl,wrap_right,temper_part,temper_part,narrow_right]
    rfl
  · rw [wrap_off _ _ member,temper_part,if_neg (gate i member)]

theorem restricted {G:Gauge}{side:Side}{V:Type}[DecidableEq V][Fintype V]{B J:Census V}
    (inc:B.choices⊆J.choices) (P:Rep G side)(rows:V→Address.Three G side)
    {H:Support side→ Config G side→Poly J}{K:Box side→ Config G side→Poly J}{o:V→Site side}
    (filed:Carton o H K P.p.threshold)(U:Config G side):
    narrow inc (density (J:=J) P rows (fun _ _=>0) (fun _ _=>0) U)=
      density (J:=B) P rows (fun _ _=>0) (fun _ _=>0) U := by
  have empty:Carton o (fun (_:Support side) (_:Config G side)=>(0:Poly J))
      (fun (_:Box side) (_:Config G side)=>(0:Poly J)) P.p.threshold:=by
    simpa only [linear,zero_smul,zero_add] using carton filed filed 0 0
  simpa only [density,narrow,map_zero,id_eq,one_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true] using
    carry_restore (passable inc) (fun _:V=>(1:ℂ)) (Φ:=fun v=>(rows v).2.1)
      (κ:=fun v=>profile P.activities (rows v).2.2) empty U

variable {G:Gauge}{C:Family G}{n m t per:ℕ}{V:Type} [DecidableEq V][Fintype V]

theorem clearance (tabs:Stock.Tabs C.path.levels) (o:V→Site (C.side n per)) (E:V→Motion) (s:V→ℕ)
    (q:ManyStem C o n→Body) (roster:Census V) (nm:n ≤ m) (mt:m ≤ t)
    (earlier:Clearance o E s (headings o E q) roster m):
    Clearance o E s (headings o E q) roster t := by
  intro z live a ha b hb ne
  have authorized:=WilsonReportHarvestUpperShadow.restored o E s q roster nm mt earlier z live
  have down:=sheltered o E roster nm mt z.val authorized
  have two:2 ≤ z.val.card:=Finset.one_lt_card.mpr ⟨a,ha,b,hb,ne⟩
  have old:=barraged o E roster down.climb (down.keep_count.symm ▸ two)
    (Mine.shelter o nm mt a) (Finset.mem_image_of_mem _ ha) (Mine.shelter o nm mt b) (Finset.mem_image_of_mem _ hb)
    (fun same=>ne (down.2 ha hb same))
  exact Mine.isolation tabs mt a.val.2 b.val.2 old

theorem opening_at (tabs:Stock.Tabs C.path.levels) (o:V→Site (C.side n per)) (E:V→Motion) (s:V→ℕ)
    (q:ManyStem C o n→Body) (roster:Census V) (nm:n ≤ m) (mt:m ≤ t)
    (earlier:Clearance o E s (headings o E q) roster m) (P:Rep G (C.side t per))
    (rows:ManyStem C o t→Address.Three G (C.side t per))
    {H:Support (C.side t per)→ Config G (C.side t per)→Poly (Mine.ward o E roster t)}
    {K:Box (C.side t per)→ Config G (C.side t per)→Poly (Mine.ward o E roster t)}
    (filed:Carton ((Mine.tree o E).supportX t) H K P.p.threshold)(U:Config G (C.side t per)):
    let dark:=shadow (Mine.tree o E) s (headings o E q) t
    let older:=WilsonMixedTaggedSeparatedBoard.admitted o E roster nm mt
    let fresh:=WilsonMixedTaggedSeparatedBoard.admitted o E roster (nm.trans mt) (le_refl t)
    opening older dark (density P rows (fun _ _=>0) (fun _ _=>0) U)=
      opening fresh dark (density P rows (fun _ _=>0) (fun _ _=>0) U) := by
  intro dark older fresh
  let full:=density (J:=Mine.ward o E roster t) P rows (fun _ _=>0) (fun _ _=>0) U
  have oldgate (z:(Mine.ward o E roster t).Mode) (miss:z.val∉(Mine.masts o E nm (barren o E roster m) t).choices):
      ¬Disjoint dark (z.val:Set _):=fun live=>miss (WilsonReportHarvestUpperShadow.restored o E s q roster nm mt earlier z live)
  have newgate:=masts_block o E s (headings o E q) (nm.trans mt) roster (clearance tabs o E s q roster nm mt earlier)
  rw [←restricted older P rows filed U,←restricted fresh P rows filed U,tempered older dark oldgate full,
    tempered fresh dark newgate full]

end YM.Integration.WilsonAllDateHarvestReopening
