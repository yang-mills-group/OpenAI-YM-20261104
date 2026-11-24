import YM.Integration.WilsonReportHarvestSlabShiftLabels

/-! The single grouped mark at capture represents the true signed three-name
coefficient on each gauge configuration, with the original grouping fee. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabShiftSingle
open Function Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open Ribbons Ribbons.ManyCopies WilsonReportHarvestSlabLabels
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {n m p N d k:ℕ} {D:Address.Rail C} {Q:ℝ}
set_option quotPrecheck false
local notation "Y" => C.path.rep N p n
local notation "σ" => Many.crust C m n d k Q
local notation "ζ" => Many.fee C m n d k 3 Q

theorem original (made:C.Makes) (tiers:Cater C D) {o:Fin 3→Site (C.side n p)}
    {rows:Fin 3→Three G (C.side n p)} {F:Config G (C.side n p)→Poly (Stock.census (Fin 3))}
    (hn:0<n) (nN:n≤N) (occ:Occupancy o (C.path.levels.clock.J n)) (positive:0<σ)
    (live:Integrable F (prior G (C.side n p))) {spend:ℝ} (furls:Furls C.path.levels n spend)
    (bill:Alcove Y rows F o (fun _=>σ) spend (Bandage.renal C.path.levels n) (1/2))
    (reach:∀i:Fin 3,coverNumber (C.path.levels.budget n).B ({o 0,o i}:Support (C.side n p))
        ≤peepers C.path.levels n) (v:Fin 3→ℂ) (bounded:∀i,‖v i‖≤1) :
    0<ζ ∧ ∃ new:Three G (C.side n p), Useful Y new ∧
      (∀U,new.1 U=(WilsonReportHarvestSlabShiftLabels.translated v (F U)).part entire) ∧
      MergeProof.Float.Blade Y (o 0) new.2.1 (profile (Y).activities new.2.2) 0 (4*(1/ζ)) := by
  have lawful:=made.wilson.represents N p n nN
  obtain ⟨registered,paid⟩:=WilsonReportHarvestSlabLabels.copy bill lawful.good live
    positive furls.eye.2.1.le (by norm_num)
  let o':Unit×Fin 3→Site (C.side n p):=o∘Prod.snd
  have copied:Occupancy o' (C.path.levels.clock.J n):=by
    intro j
    let A:=_root_.Finset.univ.filter (fun i:Unit×Fin 3=>o' i=j)
    let B:=_root_.Finset.univ.filter (fun i:Fin 3=>o i=j)
    have inj:Function.Injective (Prod.snd:Unit×Fin 3→Fin 3):=fun _ _ h=>Prod.ext (Subsingleton.elim _ _) h
    have incl:A.image Prod.snd⊆ B:=by
      intro i hi
      obtain ⟨v,hv,rfl⟩:=mem_image.mp hi
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2⟩
    exact ((card_image_of_injective A inj).ge.trans (Finset.card_le_card incl)).trans (occ j)
  have width (v:Unit×Unit):((partialGroup Unit cohort).contents v).card≤3:=
    (card_le_univ _).trans (by simp)
  obtain ⟨money,X,menu,priced⟩:=WilsonReportHarvestSlabPantry.original (Q:=Q) (m:=m) (d:=d) (k:=k)
    made tiers o' cohort (v∘Prod.snd) hn nN copied positive registered furls paid
    (fun i=>bounded i.2) (by decide) width ∅ (by simp) policy (fun v=>reach v.2)
  let i:Unit×Unit:=((),())
  refine ⟨money,X i,menu.fettled i,fun U=>?_,(priced i).2 (notMem_empty _)⟩
  have read:=(menu.check lawful.good.labels U).2 i
  exact read.symm.trans (WilsonReportHarvestSlabShiftLabels.read F v U)

end YM.Integration.WilsonReportHarvestSlabShiftSingle
