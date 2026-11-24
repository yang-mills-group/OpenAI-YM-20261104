import YM.Integration.WilsonConditionalTaylorWheelCanonicalForest
import YM.Integration.WilsonVacuumPreResetCanonicalPrefix
import YM.Integration.WilsonConditionalTaylorWheelRawVacuum

/-! Actual positive-degree pre-reset coefficients on each finite copy and its covered prescription. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetCanonicalCoil
open Function Matrix Filter Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open Comparison.RG02 FreeResolvent WilsonCoeffUV Push.Uniform
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Orb FormalBulk08.Series FormalBulk08.Jets FormalBulk08.Shore FormalBulk08.Lava FormalBulk08.Wine
open FormalBulk08.Gorge FormalBulk08.Lotus FormalBulk08.Mesa
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free Stationary
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple) (u:G.ColorIndex) (N j:ℕ)
local notation "V" => R.family.path.levels
set_option quotPrecheck false in
local notation "wood" => (fun k:ℕ=>Flat.routes (R.family.path.levels.clock.op k 0).patch)
set_option quotPrecheck false in
local notation "b" => (fun k:ℕ=>(R.family.path.levels.blocks k 0).branches)
local notation "W" => Dove.model V wood b R.metals.O u N (j+1)
local notation "P" => destination V N j



open WilsonCoeffUV.Winding
open Work.F05 UVExtension.Free FormalBulk08.Gorge FormalBulk08.Mesa
include simple in
theorem finite (live:j<N)(E e r:ℕ)(pos:0<e)(cap:e≤E)
    (previous:∀d≤E,∀k<d+2,-actionW V R.metals.O N (j+1) d (k+1)=W d (k+1))
    (tags:∀n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)
    (n:Side):
    -(coil0 V R.metals.O j N n e (r+1))=
      rancho (FormalBulk08.Bank.burn P (wood j) W R.metals.O (b j) tags n) e (r+1):=by
  let S:=primary (P).patch (V).clock.kernel n
  let F:=Reef.floor (V).clock.kernel P (wood j) n
  let Y:=freeForms V N (j+1)
  let Z:=freeForms V N j
  let M:=installed S.ratio (predictionA V N j)
  let X:=emera (actionW V R.metals.O N (j+1)) (n*(P).patch.L)
  let raw:=winter S F Y Z M R.metals.O X
  let H:=Reef.ferry P (b j) (wood j) n
  let J:=Mesa.stone W (n*(P).patch.L)
  have fold:Through E (-flash X) J:=
    WilsonVacuumPreResetCanonicalPrefix.retained R simple N (j+1) (by omega) W E previous _
  have dossier:=(Dove.genu V wood b R.metals.O u R.alloy.B.ratio simple (i:=j+1) (N:=N) live).toStory
  have head:coeff 0 J=Reef.crunch (Reef.kernelP G (V).clock.kernel.penalty (P).wing _):=by
    obtain ⟨s,C,hs,hc,hv,-⟩:=colors G (V).clock.kernel.penalty (V).clock.kernel.penalty_pos (P).legal
    exact Mesa.stoned_main hs.le hc.le (hv _).1 dossier.toVivid dossier.ink _
  have realHead:coeff 0 (-flash X)=Reef.crunch (Reef.kernelP G (V).clock.kernel.penalty (P).wing _):=
    (fold 0 (Nat.zero_le _)).trans head
  have old:=emera_far V simple R.alloy.B.ratio (Nat.succ_le_iff.mpr live) (n*(P).patch.L)
  have marg:=WilsonVacuumPreResetCanonicalBlock.observed P (b j) (wood j) n R.metals.O R.alloy.B.ratio
    ((V).clock.adm j) (tags n) Y rfl X old.1 realHead
  have heard:WilsonCoeffUV.inside S F Y M R.metals.O X=Orb.vocal H (Reef.flush F (tags n) R.metals.O (-flash X)):=marg
  have solved:=Reef.consolidate P R.metals.O (b j) (wood j) n R.alloy.B.ratio (tags n)
    (-flash X) realHead ((V).clock.adm j)
  have fare:=WilsonVacuumPreResetCanonicalPrefix.propagated F (tags n) R.metals.O H fold solved e cap
  have shape:shellK 2 raw:=winter_band S F Y Z M R.alloy.B.ratio old.1
  have purity:∀d,Pure (raw d):=winter_pure S F Y Z M R.alloy.B.ratio (b j) old.2 (age_sym V ..)
  have bankSide:coil0 V R.metals.O j N n=raw:=by
    change winter S (repeatF S) Y Z M R.metals.O X=raw
    have fix:repeatF S=F:=WilsonConditionalTaylorWheelCanonicalForest.original S
    rw [fix]
  have text:-flash raw=covelog (Orb.vocal H (Reef.flush F (tags n) R.metals.O (-flash X)))-
      orbC (precisionC G n Z)-soil (plugζ S R.metals.O):=by
    rw [show raw=winter S F Y Z M R.metals.O X from rfl,
      winter_read S F Y Z M old.1 R.alloy.B.ratio (b j) (age_sym V ..) old.2,
      WilsonConditionalTaylorWheelRawVacuum.logarithm _ (inside_mass S F Y M R.alloy.B.ratio),heard]
    abel
  rw [bankSide,←WilsonVacuumPreResetIndependentCoil.signed raw 2 shape purity e (r+1),text]
  change canyon (r+1) (coeff e (_-_ -_))=canyon (r+1) (coeff e (PowerSeries.C H.main+
    covelog (Orb.vocal H (Reef.flush F (tags n) R.metals.O J))))
  simp only [map_sub,map_add,orbC,coeff_C,if_neg pos.ne',zero_add,sub_zero,soil,coeff_map]
  have scalar:marble (r+1) (MvPolynomial.C (coeff e (plugζ S R.metals.O)):MvPolynomial (wire G n) ℝ)=0:=
    (marble_eq_zero_iff ..).mpr (MvPolynomial.homogeneousComponent_eq_zero _ _ (by simp))
  change _-marble (r+1) (MvPolynomial.C (coeff e (plugζ S R.metals.O)))=_
  rw [scalar,sub_zero,fare]

include simple in
theorem original (live:j<N)(E e r:ℕ)(pos:0<e)(cap:e≤E)
    (previous:∀d≤E,∀k<d+2,-actionW V R.metals.O N (j+1) d (k+1)=W d (k+1))
    (tags:∀n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices):
    -freshet V R.metals.O N j e (r+1)=FormalBulk08.Bank.waken P (wood j) W R.metals.O (b j) e (r+1):=
  WilsonVacuumPreResetIndependentCoil.from_finite R simple u N j live e r tags (fun per=>
    finite R simple u N j live E e r pos cap previous tags (R.family.side j per))

end YM.Integration.WilsonVacuumPreResetCanonicalCoil
