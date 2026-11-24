import YM.Integration.WilsonIndependentMatchedNamedPair
import YM.Integration.WilsonPositionProgramMasterBirth
import YM.Integration.WilsonIndependentGroupedOrbit

/-! Realize a complete derivative-indexed top verse on the actual finite
inversion board. Each term keeps its own valence, numerical verse coefficient,
test jet and named section; all fields use the layout of this one sample. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedTopFilm
open Finset Lattice RG Wilson Source Labels PhysicalNext.Repeat.Legato XSpace XSpace.Rose XSpace.Cirrus
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Bank WilsonCoeffUV.Power PowerSeries PertExtension Orb.SlotEvaluation FVA2
open WilsonIndependentMatchedNamedPair (sectionAt placed printed ranked)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(W:Initialize G)(Y:Sample 2)
local notation "T" => W.tree Y.F.p
local notation "F" d:max => R.family.labels.level d
variable {d D:ℕ}

def dose (w:d<D)(v:Verse (F d))(b:Volume D)(s:Alma (F d)) : PowerSeries ℂ :=
  FVA2.TaylorWick.into (v s) * PowerSeries.C ((jewelBloom w s b:ℝ):ℂ)

/-- The derivative-marked finite sum of rank-normalized original group letters. -/
def word (survey:Bool)(slot:Fin 2)(w:d<D)(v:Verse (F d))(b:Volume D) : Bare.Series T G :=
  ∑ s, Bare.scalar T (dose R w v b s) * printed R W Y survey d (Y.layout slot) (sheet (F d) s)

/-- The covering Peaked stencil and the actually sampled translated group
observable are the same polynomial on group fields. -/
theorem recentered (survey:Bool)(slot:Fin 2)(s:Alma (F d)) :
    Plies (sectionAt R W survey d) (sheet (F d) s) Y.F.p.side =
      fun a => placed R W Y survey d (Y.layout slot) (sheet (F d) s)
        (translate (-(chartV Y slot)) (mantle a)) := by
  funext a
  change _ = ((sectionAt R W survey d).places _ (chartV Y slot)
    (translate (-(chartV Y slot)) (mantle a))).re
  rw [SectionData.places_trans,add_neg_cancel]

/-- Common-rank clearing after the whole fitted verse has been planted. -/
theorem cleared (survey:Bool)(slot:Fin 2)(w:d<D)(v:Verse (F d))(b:Volume D) :
    X^WilsonPositionProgramMasterBirth.rank R (d:=d) * word R W Y survey slot w v b =
      ∑ s, X^(WilsonPositionProgramMasterBirth.rank R (d:=d)-valence (F d) s) *
        Bare.scalar T (dose R w v b s) *
        BareOrb.stencil T (placed R W Y survey d (Y.layout slot) (sheet (F d) s)) := by
  unfold word
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro s _
  have le : valence (F d) s ≤ WilsonPositionProgramMasterBirth.rank R (d:=d) :=
    Finset.le_sup (f:=valence (F d)) (mem_univ s)
  have clear:=ranked R W Y survey d (Y.layout slot) (sheet (F d) s)
  change X^(valence (F d) s) * _ = _ at clear
  rw [←clear]
  conv_lhs => rw [←Nat.sub_add_cancel le,pow_add]
  ring

end YM.Integration.WilsonIndependentMatchedTopFilm
