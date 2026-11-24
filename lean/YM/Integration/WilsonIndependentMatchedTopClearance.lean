import YM.Integration.WilsonIndependentMatchedTopWard

/-! Price a genuine signed equation against an occupied fitted peer. The
two opposite edges in the inversion board test exactly that peer's support. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedTopClearance
open Finset Lattice RG Wilson Source Labels PowerSeries PertExtension PertExtension.Orb XSpace
open FormalOPE.RG10 FormalOPE.RG10.InversionTop FormalOPE.RG10.InversionWard
open XSpace.Rose XSpace.Cirrus FVA2 PhysicalNext.Repeat.Legato SlotEvaluation
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Bank WilsonCoeffUV.Power
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Blue
open WilsonIndependentMatchedNamedPair (sectionAt placed printed admitted ranked)
open WilsonIndependentMatchedTopFilm (dose word)
open WilsonIndependentMatchedTopWard (force)
open scoped BigOperators Classical
variable {G:Gauge}(R:Run G)(W:Initialize G)(Y:Sample 2)
local notation "T" => W.tree Y.F.p
variable {d D:ℕ}(f:Edge (Site Y.F.p.side))(Z:Config G Y.F.p.side→G.Color)(grant:Direction f Z)
  (survey:Bool)(i:Fin 2)
local notation "S" => sectionAt R W survey d
include grant

theorem one (a:(R.family.labels.level d).Index)(clear:off f ((sectionAt R W survey d).footprint (chartV Y i))) :
    Bare.normalized T G (force T f Z * printed R W Y survey d (Y.layout i) a)=0 := by
  let O:=placed R W Y survey d (Y.layout i) a
  have proxy:Proxy O := (field_proxy _ S (Pi.single a 1) (chartV Y i)).after Complex.reCLM Complex.reCLM.contDiff
  have localO:LocalOn ((sectionAt R W survey d).footprint (chartV Y i)) O := fun U V eq =>
    congrArg Complex.re ((sectionAt R W survey d).placed_local (chartV Y i) (Pi.single a 1) U V eq)
  have zero:=WilsonIndependentMatchedTopWard.silent T f Z grant proxy
    (admitted R W Y survey d (Y.layout i) a) localO clear
  let r:=((R.family.labels.level d).grades a).2
  have eq:(X:PowerSeries ℂ)^r*Bare.normalized T G (force T f Z*printed R W Y survey d (Y.layout i) a)=0 := by
    rw [←Bare.normalized_scalar]
    have sc:Bare.scalar T (X^r) = (X:Bare.Series T G)^r := by
      simp only [Bare.scalar,map_pow,PowerSeries.map_X]
    rw [sc,mul_left_comm,ranked]
    exact zero
  exact (mul_eq_zero.mp eq).resolve_left (pow_ne_zero _ PowerSeries.X_ne_zero)

/-- No division is applied to the individual occupied terms. The exact
ordinary signed matrix row keeps every lower and scalar feed. -/
theorem original (w:d<D)(v:Verse (R.family.labels.level d))(b:Volume D)
    (clear:off f ((sectionAt R W survey d).footprint (chartV Y i))) :
    Bare.normalized T G (force T f Z * word R W Y survey i w v b)=0 := by
  rw [word,Finset.mul_sum,map_sum]
  apply Finset.sum_eq_zero
  intro s _
  rw [mul_left_comm,Bare.normalized_scalar,one R W Y f Z grant survey i _ clear,mul_zero]

end YM.Integration.WilsonIndependentMatchedTopClearance
