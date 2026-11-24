import YM.Integration.WilsonOriginalElectedForestFlag
import YM.Integration.WilsonOriginalPrimerReplicatedInk
import YM.Integration.WilsonNeutralDisplacedAngular

/-! The genuine normalized original Gaussian sends the complete additive marked page to the sum 
of the displaced readings, on the very same held field, forest and tag. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPrimerFiledPages
open Function Finset Lattice RG Wilson Tree Stationary PhysicalNext.Repeat.Legato FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove 
open Exterior Lotus Shore Gorge Rift Lava Kemp Pose Glide Dawn Rial Roof
open Planned.PrimaryIntegral295 Source Source.Drops Labels PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonOlderFreshGraphPainter
open WilsonNeutralNormalizedForestStep (chamber)
open scoped Classical Topology BigOperators Matrix
variable {G:Gauge}{d D:ℕ}(R:Run G)(a:hue G)(depth:d<D)

def sites {n:Side}(x:Site n)(m:Side):Site m:=if h:n=m then h ▸ x else 0
@[simp] theorem own {n:Side}(x:Site n):sites x n=x:=by simp [sites]

local notation "V" => R.family.path.levels
local notation "wood" => (fun j:ℕ=>Flat.routes (R.family.path.levels.clock.op j 0).patch)
local notation "br" => (fun j:ℕ=>(R.family.path.levels.blocks j 0).branches)

theorem marked (N i:ℕ)(hi:i<N)(b:Letter (R.family.labels.level d))(f:Studio D)(n:Side)(x:Site n):
    flash (WilsonElectedPrimaryTensor.chart R wood a depth (i+1) b (⟨N,hi⟩,f) n x)=
      Kemp.resite x (Kemp.banner d (Primer.fieldCoeffs R.family a wood depth N (i+1) b f) n):=by
  have e:WilsonOriginalPlacedPrimerInk.offset (G:=G) x = fun j:wire G n=>Lotus.tint x j:=by
    funext j
    exact Prod.ext (add_comm _ _) rfl
  simp only [WilsonElectedPrimaryTensor.chart,WilsonOriginalPlacedPrimerInk.origin,Kemp.resite,e]

private theorem sum_flag {X I Y:Type} [Fintype X][DecidableEq X]
    (H:Orb.Hull X I)(U:Pap (X ⊕ I))(T:Y→Pap (X ⊕ I))(s:Finset Y):
    Orb.flag H U (∑u∈s,T u)=∑u∈s,Orb.flag H U (T u):=by
  simp only [Orb.flag,map_sum,Finset.mul_sum]

variable {U:ℕ→ℕ}(grant:WilsonWindowFormalPurchase.Canonical U R.kit)
variable (N i per:ℕ)(hi:i<N)
local notation "S" => WilsonVacuumPreResetStationaryChange.step R i per
local notation "n₀" => coarse R i per
local notation "f₀" => fine R i per
local notation "P₀" => destination V N i

include grant in
theorem original (tags:∀j n,(primary ((V).clock.op j 0).patch (V).clock.kernel n).Choices)
    (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (F:Forest (S).ratio):
    ∃F':Forest (Flat.primary (P₀).patch (V).clock.kernel n₀).ratio,HEq F F' ∧
    ∀(tag:(Flat.primary (P₀).patch (V).clock.kernel n₀).Choices)
    (b:Letter (R.family.labels.level d))(f:Studio D) {J:Type} [Fintype J] (z:J→Site f₀),
    let old:=fun x:Site f₀=>WilsonElectedPrimaryTensor.chart R wood a depth (i+1) b (⟨N,hi⟩,f) f₀ x
    flash (WilsonOriginalFoldedMarkedRightColumn.filed R N i per F d (∑j,old (z j)))=
      ∑j,WilsonNeutralDisplacedAngular.reading R wood a depth N i n₀ F' tag b f (sites (z j) (n₀*(P₀).L)):=by
  obtain ⟨F',hf,read⟩:=WilsonOriginalElectedForestFlag.original R N i per a tags simple v funded hi F
  refine ⟨F',hf,?_⟩
  intro tag b f J _ z old
  let rows (n:Side) (k:J) := WilsonElectedPrimaryTensor.chart R wood a depth (i+1) b (⟨N,hi⟩,f) n (sites (z k) n)
  have admitted (n:Side)(j:J):=WilsonElectedPrimaryTensor.admitted R wood a depth (i+1) b
    (⟨N,hi⟩,f) n (sites (z j) n)
  have all (n:Side):=WilsonOriginalPrimerReplicatedInk.assembled (rows n)
    (fun j=>(admitted n j).1) (fun j=>(admitted n j).2) Finset.univ
  let bank:Crude G:=fun n=>∑k,rows n k
  have got:=read tag d bank (all _).1 (all _).2.1
  have start:bank f₀=∑k,old (z k):=by simp only [bank,rows,own,old]
  rw [←start,got]
  change Orb.flag _ (Reef.flush F' tag R.metals.O _) (Reef.seat F' (flash (∑j,rows _ j)))=_
  rw [(all _).2.2,Reef.seat,map_sum,map_sum,sum_flag]
  apply Finset.sum_congr rfl
  intro j _
  rw [WilsonNeutralAppointedForestStep.vacuum R wood a grant N (i+1),show flash (rows _ j)=_ from marked R a depth N i hi b f _ _]
  rfl

end YM.Integration.WilsonOriginalPrimerFiledPages
