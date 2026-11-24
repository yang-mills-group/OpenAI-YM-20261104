import YM.Integration.WilsonMarkedIndependentMixedCapture
import YM.WilsonCoeffUV.Marked.Capture.AtSensor

/-! The compact reporter has the very same original full test, including
all child residues and every partition, on both its finite and cover sides.
The diameter is determined by the issued test before the periods and tops. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentMixedMeasurement
open Function Filter Finset Lattice RG Wilson Laurent Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Shard WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Carp
open Source Source.Drops Labels
open WilsonMarkedIndependentMixedCompact (clipped subprice)
open scoped Classical BigOperators Topology
variable {G:Gauge}{ι:Type}[DecidableEq ι][Fintype ι]{D:ι→ℕ}

def span (F:Garland D)(y u:ℝ):ℕ:=(boxes u y F).sup fun p=>crestCard p univ

theorem heard (Y:Outerm G D)(k:ι→ℕ)(F:Garland D)(z:CellR)(u y:ℝ){M:ℕ}(cap:span F y u≤M):
    Finale u y z F k (AuthSum (clipped M Y))=Finale u y z F k (AuthSum Y):=by
  apply sum_congr rfl
  intro p hp
  have bound:crestCard p univ≤M:=(Finset.le_sup (f:=fun p=>crestCard p univ) hp).trans cap
  have equal:levelsO (clipped M Y p) univ=levelsO (Y p) univ:=by
    apply levels_g
    intro J sub
    rw [clipped,if_pos ((subprice p sub).trans bound)]
  unfold scrollR AuthSum
  rw [equal]

theorem path (L:Levels G)(O:ChartRatio G)(simple:G.Simple)(scheme:LocalRatio O)
    (Y:Outerm G D)(k:ι→ℕ)(law:Wellness k Y)(F:Garland D)(z:CellR)(y:ℝ)
    (N m b:ℕ)(top:m≤N)(later:b ≤ m)(M:ℕ)(wide:span F y 1≤M):
    Finale (paceT L.S m b) y z F k (AuthSum (Gears L O k k N m b (clipped M Y)))=
    Finale (paceT L.S m b) y z F k (AuthSum (Gears L O k k N m b Y)):=by
  rw [portsEq L O simple scheme later top z m _ F (WilsonMarkedIndependentMixedCompact.healthy M law),
    portsEq L O simple scheme later top z m _ F law,pace_self,heard Y k F z 1 y wide]

/-- Exact tested complete bank at every fixed later capture. The nested
independent LodeStar includes the scalar and the entire conditional product. -/
theorem lode {a e:ℕ}{E W V:Credit}(Q:Realm G (e+1) E)(H:Hol G)(T:Fin (a+1)→SealR G)
    (P:Tribe Q H W V T)(m N b M:ℕ)(anchor:Q.anchor ≤ m)(top:m≤N)(later:b ≤ m)
    (X:Herit T)(F:Wilt T)(z:CellR)(y ρ:ℝ)(wide:span F y 1≤M)
    (apart:∀i j,i≠j → ClearDay (F i) (F j) (ρ+14)):
    let L:=Q.draws
    let O:=Q.paid
    let k:=asp T
    let Y:=outset Q m N ρ k k (coatA L O N m T X)
    Finale (paceT L.S m b) y z F k (AuthSum (Gears L O k k N m b (clipped M Y)))=
      locale z (LodeStar L O F X m b N y):=by
  intro L O k Y
  have well:Wellness k Y:=reserveSpec L.S m m ρ (Cog L O (K':=k) le_rfl _ (cloister P X anchor top) Q.hG Q.green top)
  rw [path L O Q.hG Q.green Y k well F z y N m b top later M wide]
  exact close_eq Q H T P anchor top X F z y later apart

end YM.Integration.WilsonMarkedIndependentMixedMeasurement
end
