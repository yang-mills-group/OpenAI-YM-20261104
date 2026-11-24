import YM.Integration.WilsonIndependentMatchedTopClearance
import YM.Integration.WilsonIndependentMatchedTopPair

/-! Exact contact on the tested peer, with its entire fitted thermal verse
and independent rank shifts, even when an actual directed edge reaches it. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedTopContacts
open Finset Lattice RG Wilson Source Labels PowerSeries PertExtension PertExtension.Orb XSpace
open FormalOPE.RG10 FormalOPE.RG10.InversionTop FormalOPE.RG10.InversionWard
open XSpace.Rose XSpace.Cirrus FVA2 PhysicalNext.Repeat.Legato SlotEvaluation
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Bank WilsonCoeffUV.Power WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard
open WilsonIndependentMatchedNamedPair (sectionAt placed admitted)
open WilsonIndependentMatchedTopFilm (word)
open WilsonIndependentMatchedTopPair (clearedDose)
open WilsonIndependentMatchedTopWard (force)
open scoped BigOperators Classical
variable {G:Gauge}(R:Run G)(W:Initialize G)(Y:Sample 2)
local notation "T" => W.tree Y.F.p
local notation "F" h:max => R.family.labels.level h
local notation "rnk" h:max => WilsonPositionProgramMasterBirth.rank R (d:=h)
variable {d D:ℕ}

theorem original (f:Edge (Site Y.F.p.side))(Z:Config G Y.F.p.side→G.Color)
    (grant:Direction f Z)(survey:Bool)(i:Fin 2)(w:d<D)(v:Verse (F d))(b:Volume D) :
    X^(rnk d) * Bare.normalized T G (force T f Z * word R W Y survey i w v b) =
      ∑s,clearedDose R w v b s * (X^2 * Bare.normalized T G
        (BareOrb.stencil T (coupled f Z (placed R W Y survey d (Y.layout i) (sheet (F d) s))))) := by
  let eqn:=force T f Z
  have put:Bare.scalar (G:=G) T (X^(rnk d))=X^(rnk d):=by simp only [Bare.scalar,map_pow,PowerSeries.map_X]
  rw [←Bare.normalized_scalar,put,mul_left_comm,WilsonIndependentMatchedTopPair.cleared,Finset.mul_sum,map_sum]
  refine sum_congr rfl (fun s _=>?_ )
  rw [mul_left_comm,Bare.normalized_scalar]
  apply congrArg (clearedDose R w v b s * ·)
  let a:=sheet (F d) s
  let O:=placed R W Y survey d (Y.layout i) a
  have proxy:Proxy O := (field_proxy _ (sectionAt R W survey d) (Pi.single a 1) (chartV Y i)).after
    Complex.reCLM Complex.reCLM.contDiff
  exact WilsonIndependentMatchedTopWard.hearing T f Z grant proxy (admitted R W Y survey d (Y.layout i) a)

/-- Each genuinely filed local equation can carry its own sign, derivative
and finite thermal dose. -/
theorem separated {J:Type} [Fintype J](edges:J→Edge (Site Y.F.p.side))
    (vectors:J → Config G Y.F.p.side→G.Color)(grant:∀j,Direction (edges j) (vectors j))
    (c:J→PowerSeries ℂ)(survey:Bool)(i:Fin 2)(w:d<D)(v:Verse (F d))(b:Volume D)
    (clear:∀j,off (edges j) ((sectionAt R W survey d).footprint (chartV Y i))) :
    Bare.normalized T G ((∑j,Bare.scalar T (c j)*force T (edges j) (vectors j))*
      word R W Y survey i w v b)=0 := by
  rw [Finset.sum_mul,map_sum]
  refine sum_eq_zero (fun j _=>?_ )
  rw [mul_assoc,Bare.normalized_scalar,WilsonIndependentMatchedTopClearance.original
    R W Y (edges j) (vectors j) (grant j) survey i w v b (clear j),mul_zero]

end YM.Integration.WilsonIndependentMatchedTopContacts
