import YM.Integration.WilsonPointChildGazette
import YM.Integration.WilsonMarkedIndependentFoldedBirth
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildFiledSeam
open Function Filter Finset Lattice RG Wilson Laurent Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.ScaleS
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Embroider WilsonCoeffUV.Shard WilsonCoeffUV.Winding
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonConditionalTaylorSeparatedPurchase (fee)
open scoped Classical BigOperators
open WilsonPointChildScalarSlot
open Function Filter Finset Lattice Wilson RG Precision Laurent Source Labels Marker WilsonCoeffUV
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding
open AnalyticNext.QuarticMatch.Sheets IndependentSourcePathFamily
open scoped Classical BigOperators
open WilsonPointChildGazette
variable {G:Gauge}

def folded (L:Levels G)(O:ChartRatio G)(j N d:ℕ)(X:Era G ℝ)(n:Side):=
  let P:=loose L j
  let f:=n*P.L
  Blue.mix (ratioHigh L O N j) (reed (stepAt P L.clock.kernel n) (xree P L.clock.kernel n)
    (freeForms L N (j+1)) (roam L N j n) O (emera (actionW L O N (j+1)) f) d
    (fun e r=>Carp.plume (X.2 e r) f))

private theorem mapping {d:ℕ}{X:Era G ℝ}(authorized:Auth d X)(n:Side)(e r:ℕ):
    Carp.plume ((tuftV inlet X).2 e r) n=inlet ∘ Carp.plume (X.2 e r) n:=by
  obtain ⟨s,C,pos,bound⟩:=(authorized.wing e r).land
  exact Carp.plume_map _ bound pos inlet n

theorem forecast (L:Levels G)(O:ChartRatio G)(j N d:ℕ)(n:Side)(live:j<N)(simple:G.Simple)
    (good:LocalRatio O)(X:Era G ℝ)(authorized:Auth d X)(e r:ℕ):
    Carp.plume ((logO L O j N (roster X) (born d) {()}).2 e r) n=
      inlet ∘ Carp.plume ((verseI L O j N d X).2 e r) n:=by
  have mass₁:mass (born d) {()}=d:=by simp [mass,born]
  rw [WilsonMarkedIndependentNormalizedRecursion.singleton L O j N live simple good (roster X)
      (legal authorized) (empty X) (),full,mass₁,←ply_verse L live simple good authorized]
  exact mapping (Auth.verse L live simple good authorized) n e r

theorem physical (L:Levels G)(O:ChartRatio G)(j N d:ℕ)(n:Side)
    (X:Era G ℝ)(authorized:Auth d X):
    coilH L O j N n (roster X) (born d) (ratioHigh L O N j) {()} =
      ply inlet.toLinearMap (folded L O j N d X n):=by
  have mass₁:mass (born d) {()}=d:=by simp [mass,born]
  let P:=loose L j
  let f:=n*P.L
  have lower:((repaint (roster X)) {()}).1 f=ply inlet.toLinearMap (fun e r=>Carp.plume (X.2 e r) f):=by
    funext e r
    change Carp.plume (((roster X) {()}).2 e r) f=inlet ∘ Carp.plume (X.2 e r) f
    rw [full];exact mapping authorized f e r
  rw [WilsonMarkedIndependentFoldedBirth.singleton L O j N n () (roster X) (legal authorized) (empty X)
    (ratioHigh L O N j),mass₁,lower,folded,ply_mixX]
  apply congrArg (Blue.mix (ratioHigh L O N j))
  exact (reed_maps _ _ _ _ d inlet.toLinearMap).symm

/-- The native charged singleton and its scalar output use the identical full
quiet numerator, same reversion and same individually placed finite root. -/
theorem read (L:Levels G)(O:ChartRatio G)(j N d:ℕ)(n:Side)(live:j<N)(simple:G.Simple)(good:LocalRatio O)
    (X:Era G ℝ)(authorized:Auth d X)(e r:ℕ)(x):
    let Z:=logO L O j N (roster X) (born d) {()}
    let V:=coilH L O j N n (roster X) (born d) (ratioHigh L O N j) {()}
    outlet ((Carp.plume (Z.2 e r) n-V e r) x)=
      Carp.plume ((verseI L O j N d X).2 e r) n x-folded L O j N d X n e r x:=by
  change outlet ((Carp.plume ((logO _ _ _ _ _ _ _).2 e r) n) x-(coilH _ _ _ _ _ _ _ _ _) e r x)=_
  rw [forecast L O j N d n live simple good X authorized e r,physical L O j N d n X authorized,map_sub]
  exact congrArg₂ (·-·) (WilsonPointChildScalarSlot.submitted _) (WilsonPointChildScalarSlot.submitted _)

end YM.Integration.WilsonPointChildFiledSeam
