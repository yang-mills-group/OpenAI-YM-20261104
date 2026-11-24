import YM.Integration.WilsonNeutralObservedCover
import YM.FormalBulk08.Sierra.Park

/-! The conditional and its cover limit at one actual fine predecessor.
No average over the other children is used. The child's submitted test is
retained throughout. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralDisplacedAngular
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free Work.F03 Work.F05 Work.F08
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato
open WilsonRunFormalMarkedStep
open scoped Topology BigOperators Matrix Classical

open WilsonNeutralNormalizedForestStep
open FVA1Physical.TwoReset Next.Foundations

section Forest
variable {G:Gauge} {K:KernelChoices} {j d:ℕ} (P:Flight j d) (h:P.patch.Branches K G) (n:Side)
variable (F:Forest (primary P.patch K n).ratio) (t:(primary P.patch K n).Choices)
theorem conditional (L:Lodge P.patch) (r:(primary P.patch K n).Choices) (O:ChartRatio G)
    (localO:LocalRatio O) (room:4≤d) (U T:Pap (wire G (n*P.L)))
    (head:coeff 0 U=crunch (kernelP G K.penalty P.wing _))
    (quiet:Rite U U 1 0) (insert:Rite T T 1 0) :
    Orb.flag (chamber P h n F t) (Reef.flush F t O U) (Reef.seat F T) =
      Reef.tossed P O h L n r U T := by
  rw [Turner.tossed_choice O P h L r t U T]
  let E:=Reef.floor K P L n
  exact Turner.summer_fren (Work.F05.freeEquiv F E) t O h localO _ (Reef.ferry P h L n) U quiet T insert
    (Reef.baked G K P n F room h O localO t _ rfl _ head)
    (Reef.consolidate P O h L n localO t U head room)

end Forest

variable {G:Gauge} {d D:ℕ} (R:Run G) (routes:Primer.Families R.family) (a:hue G)
variable (depth:d<D){U:ℕ→ℕ} (grant:WilsonWindowFormalPurchase.Canonical U R.kit)

def reading (run:Run G) (wood:Primer.Families run.family) (col:hue G) (Dfit:d<D)
    (N i:ℕ) (s:Side) (F:Forest (primary (destination run.family.path.levels N i).patch run.family.path.levels.clock.kernel s).ratio)
    (t:(primary (destination run.family.path.levels N i).patch run.family.path.levels.clock.kernel s).Choices)
    (b:Letter (run.family.labels.level d))(f:Studio D)(z:Site (s*(destination run.family.path.levels N i).L)):
    Pap (wire G s) :=by
  let A:=destination run.family.path.levels N i
  let w:=Primer.densityCoeff run.family wood col N (i+1)
  let Y:=Primer.fieldCoeffs run.family col wood Dfit N (i+1) b f
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
    let Y:=Primer.fieldCoeffs R.family a routes depth N (i+1) b f
    reading R routes a depth N i s F t b f z =
      Reef.tossed A R.metals.O (R.family.path.levels.blocks i 0).branches (routes i) s u
        (Mesa.stone w (s*A.L)) (Kemp.resite z (Kemp.banner d Y (s*A.L))) := by
  intro A w Y
  have c:=WilsonRunFormalMarkedStep.normalized R routes a depth hs o N (i+1) live
    (hd.trans (R.family.path.levels.fits.mono (Nat.le_succ _)))
  have old:=Dove.genu R.family.path.levels routes (fun k=>(R.family.path.levels.blocks k 0).branches) R.metals.O a
    R.alloy.B.ratio hs (i:=i+1) (N:=N) live
  obtain ⟨sym,C,h0,hC,stock,-⟩:=colors G R.family.path.levels.clock.kernel.penalty
    R.family.path.levels.clock.kernel.penalty_pos A.legal
  let Z:=Kemp.banner d Y (s*A.L)
  have head:=stoned_main h0.le hC.le (stock A.wing).1 old.toVivid old.ink (s*A.L)
  have lawful:Rite Z Z 1 0:=by
    dsimp only [Z,Y]
    rw [←WilsonNeutralAppointedForestStep.column R routes a depth grant]
    exact (Kemp.solo_iff ..).mp (clef_through (c.officers b) (slotsFits _ b)).ward _ _
  dsimp only [reading,w]
  rw [←WilsonNeutralAppointedForestStep.vacuum R routes a grant]
  apply conditional _ _ _ _ _ _ _ _ R.alloy.B.ratio (R.family.path.levels.clock.adm i) _ _ head (old.civic _ 1 0)
  simpa only [Signed.act_one,Z,Y] using! (Kemp.repulp (x:=z) 1 Z Z lawful)

include grant in
theorem covered (N i:ℕ)(hs:G.Simple)(o:Loc G 1)(live:i<N)(hd:d≤R.family.path.levels.clock.J (i+1))
    (n:Side)(F:∀s:Side,Forest (primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel s).ratio)
    (t:∀s:Side,(primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel s).Choices)
    (b:Letter (R.family.labels.level d))(f:Studio D)(x:Site (destination R.family.path.levels N i).L)
    (e r:ℕ)(v:chain (wire G n) r) :
    let A:=destination R.family.path.levels N i
    let w:=Primer.densityCoeff R.family routes a N (i+1)
    let Y:=Primer.fieldCoeffs R.family a routes depth N (i+1) b f
    let out:=Kemp.braise A (routes i) w (Kemp.work (lift x) Y) R.metals.O (R.family.path.levels.blocks i 0).branches d
    Tendsto (fun c:Covers R.family.path.levels.S i n=>
      let m:=WilsonNeutralReceivedCoverLimit.multiplicity R.family.path.levels.S i n c
      Shore.cores (Shore.tray m n) (rancho (reading R routes a depth N i (m*n) (F _) (t _) b f (wrap _ (lift x))) e r) v)
      (coverFilter R.family.path.levels.S i n) (𝓝 (sieve n (out e r) v)):=by
  intro A w Y out
  have c:=WilsonRunFormalMarkedStep.normalized R routes a depth hs o N (i+1) live
    (hd.trans (R.family.path.levels.fits.mono (Nat.le_succ _)))
  have ritual:Sierra.Ritual Y d:=by
    dsimp only [Y]
    rw [←WilsonNeutralAppointedForestStep.column R routes a depth grant]
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
  rw [original R routes a depth grant N i hs o live hd _ (F _) (t _) (t _) b f (wrap _ (lift x))]
  rfl

end YM.Integration.WilsonNeutralDisplacedAngular
end
