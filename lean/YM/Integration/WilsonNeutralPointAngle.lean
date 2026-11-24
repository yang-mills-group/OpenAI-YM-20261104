import YM.Integration.WilsonNeutralDisplacedAngular
import YM.Integration.WilsonNeutralPointCourse

/-! Finite forest readings on the complete independently filed single-child history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralPointAngle
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free Work.F03 Work.F05 Work.F08
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato
open WilsonRunFormalMarkedStep
open scoped Topology BigOperators Matrix Classical

open WilsonNeutralNormalizedForestStep
open FVA1Physical.TwoReset Next.Foundations

variable {G:Gauge} {d D:ℕ} (R:Run G) (routes:Primer.Families R.family) (a:hue G)
variable (depth:d<D)(digit:∀i,Site (R.family.S.block i)){U:ℕ→ℕ} (grant:WilsonWindowFormalPurchase.Canonical U R.kit)

def reading (run:Run G) (wood:Primer.Families run.family) (col:hue G) (Dfit:d<D) (digit:∀i,Site (run.family.S.block i))
    (N i:ℕ) (s:Side) (F:Forest (primary (destination run.family.path.levels N i).patch run.family.path.levels.clock.kernel s).ratio)
    (t:(primary (destination run.family.path.levels N i).patch run.family.path.levels.clock.kernel s).Choices)
    (b:Letter (run.family.labels.level d))(f:Studio D)(z:Site (s*(destination run.family.path.levels N i).L)):
    Pap (wire G s) :=by
  let A:=destination run.family.path.levels N i
  let w:=Primer.densityCoeff run.family wood col N (i+1)
  let Y:=WilsonNeutralPointCourse.filed run wood col Dfit digit N (i+1) b f
  let Z:=Kemp.banner d Y (s*A.L)
  exact Orb.flag (chamber A (run.family.path.levels.blocks i 0).branches s F t)
    (Reef.flush F t run.metals.O (Mesa.stone w (s*A.L))) (Reef.seat F (Kemp.resite z Z))

include grant in
theorem original (N i:ℕ)(hs:G.Simple)(o:Loc G 1)(live:i<N)(hd:d≤R.family.path.levels.clock.J (i+1))
    (s:Side)(F:Forest (primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel s).ratio)
    (t u:(primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel s).Choices)
    (b:Letter (R.family.labels.level d))(f:Studio D)(z:Site (s*(destination R.family.path.levels N i).L)):
    let A:=destination R.family.path.levels N i
    let w:=Primer.densityCoeff R.family routes a N (i+1)
    let Y:=WilsonNeutralPointCourse.filed R routes a depth digit N (i+1) b f
    reading R routes a depth digit N i s F t b f z =
      Reef.tossed A R.metals.O (R.family.path.levels.blocks i 0).branches (routes i) s u
        (Mesa.stone w (s*A.L)) (Kemp.resite z (Kemp.banner d Y (s*A.L))) := by
  intro A w Y
  have c:=WilsonNeutralPointCourse.original R routes a depth digit N (i+1) hs o live
    (hd.trans (R.family.path.levels.fits.mono (Nat.le_succ _)))
  have old:=Dove.genu R.family.path.levels routes (fun k=>(R.family.path.levels.blocks k 0).branches) R.metals.O a
    R.alloy.B.ratio hs (i:=i+1) (N:=N) live
  obtain ⟨sym,C,h0,hC,stock,-⟩:=colors G R.family.path.levels.clock.kernel.penalty
    R.family.path.levels.clock.kernel.penalty_pos A.legal
  let Z:=Kemp.banner d Y (s*A.L)
  have head:=stoned_main h0.le hC.le (stock A.wing).1 old.toVivid old.ink (s*A.L)
  have lawful:Rite Z Z 1 0:=by
    dsimp only [Z,Y]
    exact (Kemp.solo_iff ..).mp (clef_through (c.officers b) (slotsFits _ b)).ward _ _
  dsimp only [reading,w]
  rw [←WilsonNeutralAppointedForestStep.vacuum R routes a grant]
  apply WilsonNeutralDisplacedAngular.conditional _ _ _ _ _ _ _ _ R.alloy.B.ratio (R.family.path.levels.clock.adm i) _ _ head (old.civic _ 1 0)
  simpa only [Signed.act_one,Z,Y] using! (Kemp.repulp (x:=z) 1 Z Z lawful)

include grant in
theorem covered (N i:ℕ)(hs:G.Simple)(o:Loc G 1)(live:i<N)(hd:d≤R.family.path.levels.clock.J (i+1))
    (n:Side)(F:∀s:Side,Forest (primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel s).ratio)
    (t:∀s:Side,(primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel s).Choices)
    (b:Letter (R.family.labels.level d))(f:Studio D)(x:Site (destination R.family.path.levels N i).L)
    (e r:ℕ)(v:chain (wire G n) r) :
    let A:=destination R.family.path.levels N i
    let w:=Primer.densityCoeff R.family routes a N (i+1)
    let Y:=WilsonNeutralPointCourse.filed R routes a depth digit N (i+1) b f
    let out:=Kemp.braise A (routes i) w (Kemp.work (lift x) Y) R.metals.O (R.family.path.levels.blocks i 0).branches d
    Tendsto (fun c:Covers R.family.path.levels.S i n=>
      let m:=WilsonNeutralReceivedCoverLimit.multiplicity R.family.path.levels.S i n c
      Shore.cores (Shore.tray m n) (rancho (reading R routes a depth digit N i (m*n) (F _) (t _) b f (wrap _ (lift x))) e r) v)
      (coverFilter R.family.path.levels.S i n) (𝓝 (sieve n (out e r) v)):=by
  intro A w Y out
  have c:=WilsonNeutralPointCourse.original R routes a depth digit N (i+1) hs o live
    (hd.trans (R.family.path.levels.fits.mono (Nat.le_succ _)))
  have ritual:Sierra.Ritual Y d:=by
    dsimp only [Y]
    exact Sierra.ritual_cell o f (clef_through (c.officers b) (slotsFits _ b))
  have moved:=Sierra.from_R Y d ritual (lift x)
  have story:Story w (pink R.family.path.levels.clock.kernel.penalty A.wing):=by
    dsimp only [w]
    rw [←WilsonNeutralAppointedForestStep.vacuum R routes a grant]
    exact (Dove.genu R.family.path.levels routes (fun k=>(R.family.path.levels.blocks k 0).branches) R.metals.O a
      R.alloy.B.ratio hs (i:=i+1) (N:=N) live).toStory
  obtain ⟨η,η0,est⟩:=Sierra.testified ((0,o):edgeL G) A (routes i) w R.metals.O
    (R.family.path.levels.blocks i 0).branches story R.alloy.B.ratio (R.family.path.levels.clock.adm i) moved t e r
  refine ((Kemp.sieve_copy n est η0 v).comp (WilsonNeutralReceivedCoverLimit.growing R.family.path.levels.S i n)).congr'
    (.of_forall fun j=>?_ )
  dsimp only [Function.comp_def]
  rw [Kemp.seated (lift x) Y d _ ritual.young ritual.committees]
  rw [original R routes a depth digit grant N i hs o live hd _ (F _) (t _) (t _) b f (wrap _ (lift x))]
  rfl

end YM.Integration.WilsonNeutralPointAngle
end
