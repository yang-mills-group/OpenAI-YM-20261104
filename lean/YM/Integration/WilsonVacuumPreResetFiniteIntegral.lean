import YM.Integration.WilsonVacuumPreResetIndependentForecast
import YM.Integration.WilsonConditionalTaylorWheelRawCenter

/-! Full finite-volume vacuum with its own incoming action on the original tree. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFiniteIntegral
open Function Matrix Filter Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open Comparison.RG02 FreeResolvent WilsonCoeffUV Push.Uniform
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Orb FormalBulk08.Series FormalBulk08.Jets FormalBulk08.Shore FormalBulk08.Lava FormalBulk08.Wine
open FormalBulk08.Gorge FormalBulk08.Lotus FormalBulk08.Mesa
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free Stationary
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G)
local notation "V" => R.family.path.levels
set_option quotPrecheck false in
local notation "wood" => (fun k:ℕ=>Flat.routes (R.family.path.levels.clock.op k 0).patch)
set_option quotPrecheck false in
local notation "b" => (fun k:ℕ=>(R.family.path.levels.blocks k 0).branches)

def read (N j:ℕ) (n:Side):Pap (wire G n):= -flash ((story V R.metals.O N j).1 n)

def posted (N j:ℕ) (n:Side) (tag:(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)
    (X:Pap (wire G (n*(destination V N j).patch.L))):Pap (wire G n):=
  Reef.landed (destination V N j) R.metals.O (b j) (wood j) n tag X

theorem head (simple:G.Simple) {N j:ℕ}(live:j≤N)(n:Side):
    coeff 0 (read R N j n)=Reef.crunch (Reef.kernelP G (V).clock.kernel.penalty (location V N j) n):=by
  have enrolled:=((WilsonCoeffUV.Bank.old V R.metals.O simple R.alloy.B.ratio N j live).basis n).stem
  rw [read,map_neg,Blue.flash,coeff_mk,enrolled,visible_shine]
  exact WilsonConditionalTaylorWheelClassicalHead.kernel R N j n

theorem original (simple:G.Simple) {N j:ℕ}(live:j<N)(n:Side)
    (tag:(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices):
    let P:=destination V N j
    let S:=primary P.patch (V).clock.kernel n
    let upper:=(story V R.metals.O N (j+1)).1
    let X:=unripe V R.metals.O N j upper n
    let Y:=posted R N j n tag (read R N (j+1) (n*P.patch.L))
    (-flash X=Y-soil (plugζ S R.metals.O)) ∧ shellK 2 X ∧ ∀e,Pure (X e):=by
  intro P S upper X Y
  let F:=Reef.floor (V).clock.kernel P (wood j) n
  let inc:=freeForms V N (j+1)
  let out:=freeForms V N j
  let M:=installed S.ratio (predictionA V N j)
  let old:=upper (n*P.patch.L)
  let raw:=winter S F inc out M R.metals.O old
  let H:=Reef.ferry P (b j) (wood j) n
  have tab:=((WilsonCoeffUV.Bank.old V R.metals.O simple R.alloy.B.ratio N (j+1) live).basis (n*P.patch.L))
  have rank:shellK 2 old:=tab.lamp
  have pure:∀e,Pure (old e):=tab.shape
  have same:X=raw:=by
    change winter S (repeatF S) inc out M R.metals.O old=raw
    have fix:repeatF S=F:=WilsonConditionalTaylorWheelCanonicalForest.original S
    rw [fix]
  have leading:coeff 0 (-flash old)=Reef.crunch (Reef.kernelP G (V).clock.kernel.penalty P.wing _):=
    head R simple live (n*P.patch.L)
  have marg:WilsonCoeffUV.inside S F inc M R.metals.O old=Orb.vocal H (Reef.flush F tag R.metals.O (-flash old)):=
    WilsonVacuumPreResetCanonicalBlock.observed P (b j) (wood j) n R.metals.O R.alloy.B.ratio
      ((V).clock.adm j) tag inc rfl old rank leading
  have stem:PowerSeries.C H.main= -orbC (precisionC G n out):=by
    have physical:=WilsonConditionalTaylorWheelClassicalHead.kernel R N j n
    rw [loc_land V N j live] at physical
    have curtain:H.main= -paint 2 (orbQ (precisionC G n out)):=physical.symm
    rw [curtain,map_neg,orbC]
  rw [same]
  refine ⟨?_,winter_band S F inc out M R.alloy.B.ratio rank,
    winter_pure S F inc out M R.alloy.B.ratio (b j) pure (age_sym V ..)⟩
  change -flash raw=PowerSeries.C H.main+covelog (Orb.vocal H (Reef.flush F tag R.metals.O (-flash old)))-soil (plugζ S R.metals.O)
  rw [show raw=winter S F inc out M R.metals.O old from rfl,
    winter_read S F inc out M rank R.alloy.B.ratio (b j) (age_sym V ..) pure,
    WilsonConditionalTaylorWheelRawVacuum.logarithm _ (inside_mass S F inc M R.alloy.B.ratio),
    marg,stem]
  abel

end YM.Integration.WilsonVacuumPreResetFiniteIntegral
end
