import YM.Integration.WilsonPointChildFiniteWard
import YM.Integration.WilsonPointChildCoverReturn
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildFiniteReturn
open YM FormalBulk08 Lattice RG Laurent Next.Foundations PhysicalNext.Repeat.Legato
open Reef Flat Stationary Dawn Pose Kemp Palm Shore Mesa Wine Quire Roof Lotus Sierra Gorge Dove Rial
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped ContDiff BigOperators Topology Classical
variable {G:Gauge}{d D:ℕ}
variable (R:Run G)(u:G.ColorIndex)(depth:d<D)
variable (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)

/-- Unaliased computation on the actual finite sides. At each date the
incoming quiet state is the true finite `story.1` on this same history. -/
def table (N:ℕ):ℕ→ℕ→Letter (R.family.labels.level d)→Scroll D→(n:Side)→PChart G n
  | 0, _, v, p, n => Shore.rancho
      (Kemp.banner d ((sectionY (R.family.localSection d) depth) v (physical p)) n)
  | h+1, j, v, p, n =>
    let P:=WilsonCoeffUV.loose R.family.path.levels j
    let T:=WilsonNeutralPointCourse.transfer R (routes R) u depth (fun _=>0) N j
    Shore.rancho (∑s,Wine.worm (wire G n) ((T⁻¹) s v) *
      flash ((P.L.val^d) • WilsonMarkedFiniteIndependentStep.fixed R u tags N j n
       (table N h (j+1) s (growWord P 0 D p) (n*P.L))))

theorem result (N h j:ℕ)(v:Letter (R.family.labels.level d))(p:Scroll D)(n:Side):
    let P:=WilsonCoeffUV.loose R.family.path.levels j
    let T:=WilsonNeutralPointCourse.transfer R (routes R) u depth (fun _=>0) N j
    flash (table R u depth tags N (h+1) j v p n)=∑s,Wine.worm (wire G n) ((T⁻¹) s v) *
      flash ((P.L.val^d) • WilsonMarkedFiniteIndependentStep.fixed R u tags N j n
       (table R u depth tags N h (j+1) s (growWord P 0 D p) (n*P.L))):=
  WilsonPointChildFiniteWard.recorded _

theorem original (simple:G.Simple)(o:Loc G 1)(price:ℕ→Gear G→ℝ)
    (bought:FundedMarkedCoverRows.prices price R.kit)(N h j:ℕ)(live:j+h≤N)
    (v:Letter (R.family.labels.level d))(p:Scroll D)(n:Side):
    let Z:=flash (table R u depth tags N h j v p n)
    Rite Z Z 1 0:=by
  induction h generalizing j v p n with
  | zero=>
    have top:=Roof.topC o (R.family.labels.level d) (R.family.localSection d) R.family.params (R.makes.sections d) (Next.Foundations.valuation G d) depth
    have birth:=((solo_iff ..).mp (clef_through (top.officers v) (slotsFits _ v)).ward) n (physical p)
    change Rite (flash (Shore.rancho _))
      (flash (Shore.rancho _)) 1 0
    simpa only [WilsonPointChildFiniteWard.recorded] using birth
  | succ h ih=>
    let P:=WilsonCoeffUV.loose R.family.path.levels j
    let T:=WilsonNeutralPointCourse.transfer R (routes R) u depth (fun _=>0) N j
    let U(s:Letter (R.family.labels.level d)):=table R u depth tags N h (j+1) s (growWord P 0 D p) (n*P.L)
    have terms(s:Letter (R.family.labels.level d)):=WilsonPointChildFiniteWard.step R u tags simple price bought
      (N:=N) (j:=j) (by omega) n (U s) (ih (j+1) (by omega) _ _ _) (P.L.val^d)
    change Rite (flash (table R u depth tags N (h+1) j v p n))
      (flash (table R u depth tags N (h+1) j v p n)) 1 0
    rw [result]
    intro V inst a b k ac bc ha hb hk hz hold
    simp only [map_sum,map_mul,Wine.worm_roam]
    apply Finset.sum_congr rfl
    intro s hs
    rw [terms s V a b k ac bc ha hb hk hz hold]

end YM.Integration.WilsonPointChildFiniteReturn
