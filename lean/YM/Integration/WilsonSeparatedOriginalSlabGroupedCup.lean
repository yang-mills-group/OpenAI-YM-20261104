import YM.Integration.WilsonReportHarvestSlabSingle
import YM.OPE.Portfolio.Cup

/-! The actual grouped Wilson three-name coefficient as an original one-source portfolio. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabGroupedCup
open Function Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Cadet WilsonReportHarvestSlabLabels
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {m p N d k:ℕ} {D:Address.Rail C} {Q:ℝ}
set_option quotPrecheck false

private def install {n:Side}{Y:Rep G n}(x:Three G n)(hx:Useful Y x):Cup Y:=
  Cup.book Y x.2.1 x.2.2 hx.normK

theorem returned {n:ℕ}(made:C.Makes)(hn:n≤N) (x:Three G (C.side n p))
    (hx:Useful (C.path.rep N p n) x): (install x hx).pays=x.1:=by
  let Y:=C.path.rep N p n
  let X:=install x hx
  have same:profile Y.activities X.chosen=profile Y.activities x.2.2:=X.fitted.symm
  exact (MergeProof.Float.coin_port Y x.2.1 X.held hx.normK same
    (made.wilson.represents N p n hn).good.labels).trans hx.read

variable {b:ℕ}
local notation "Y"=>C.path.rep N p (b+1)
local notation "σ"=>Many.crust C m (b+1) d k Q
local notation "ζ"=>Many.fee C m (b+1) d k 3 Q
local notation "A"=>C.S.oneStep b p

theorem original (made:C.Makes)(tiers:Cater C D){o:Fin 3→Site (C.side (b+1) p)}
    {rows:Fin 3→Three G (C.side (b+1) p)}{F:Config G (C.side (b+1) p)→Poly (Stock.census (Fin 3))}
    (nN:b+1≤N)(occ:Occupancy o (C.path.levels.clock.J (b+1)))(positive:0<σ)
    (live:Integrable F (prior G (C.side (b+1) p))){spend:ℝ}(furls:Furls C.path.levels (b+1) spend)
    (bill:Alcove Y rows F o (fun _=>σ) spend (Bandage.renal C.path.levels (b+1)) (1/2))
    (reach:∀i:Fin 3,coverNumber (C.path.levels.budget (b+1)).B ({o 0,o i}:Support (C.side (b+1) p))
      ≤peepers C.path.levels (b+1)):
    0<ζ ∧ ∃X:Cup Y, (∀U,X.pays U=(F U).part entire) ∧
      MergeProof.Float.Blade Y ((A).assemble ((A).parent (o 0),(A).residue (o 0)))
        X.home X.leaves 0 (4*(1/ζ)):=by
  obtain ⟨fee,x,hx,eqn,blade⟩:=WilsonReportHarvestSlabSingle.original made tiers (Nat.zero_lt_succ b)
    nN occ positive live furls bill reach
  refine ⟨fee,install x hx,fun U=>(congr_fun (returned made nN x hx) U).trans (eqn U),?_⟩
  have placed:(A).assemble ((A).parent (o 0),(A).residue (o 0))=o 0:=by
    rw [(A).unpack]; exact (A).splitSites.symm_apply_apply _
  rw [placed]
  exact blade

end YM.Integration.WilsonSeparatedOriginalSlabGroupedCup
