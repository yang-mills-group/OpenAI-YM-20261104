import YM.Integration.WilsonIndependentMatchedNamedPair
import YM.RegulatorIR.Profiles.Staple

/-! Each conventional or surveyed Wilson direction has one fixed cover
stencil. Translate this same symbol to each actual finite orbit address. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentRawNamedStencil
open Lattice RG Source Labels PertExtension Orb XSpace XSpace.Rose XSpace.Cirrus
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Halo
open RegulatorIR.Profiles RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.Step RegulatorIR.Prim RegulatorIR.Cluster RegulatorIR.Diagram FVA2 PhysicalNext.Repeat.Legato
open WilsonIndependentMatchedNamedPair
open scoped Classical

variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
local notation "F" d:max => R.family.labels.level d

def brand (a:Bool)(d:ℕ)(b:(F d).Index) :=
  Profiles.bare (sectionAt R W a d) b

theorem authentic (a:Bool)(d:ℕ)(b:(F d).Index) :
    LocalStamp (brand R W a d b) ((F d).grades b).2 := by
  cases a with
  | false => exact authentically _ (R.makes.sections d) (FVAAlt2.Block.clothes R d) b
  | true =>
    have h:=WilsonOriginalPivotWardSurvey.issued R W d
    exact authentically _ h.1 h.2.1 b

def tensor (a:Bool)(d:ℕ)(b:(F d).Index) : Orders (Foot G) :=
  (stamp_symbol (authentic R W a d b)).choose

def shifted (a:Bool)(d:ℕ)(b:(F d).Index)(o:Cover) : Orders (Foot G) :=
  fun i r=>echo (carryX o) (tensor R W a d b i r)

theorem named (a:Bool)(d:ℕ)(b:(F d).Index)(o:Cover) :
    let h:=((F d).grades b).2
    BasisT h h (convey o (brand R W a d b)) (shifted R W a d b o) ∧
      Ranks h (shifted R W a d b o) := by
  intro h
  obtain ⟨H,N⟩:=
    (stamp_symbol (authentic R W a d b)).choose_spec
  refine ⟨H.vayne o,?_⟩
  intro i j alive
  apply N i j
  intro dead
  apply alive
  exact (congrArg (echo (carryX o)) dead).trans echo_zero

theorem submitted (a:Bool)(d:ℕ)(b:(F d).Index)(o:Cover)(Y:Sample 2) :
    vital Y.F.p.side (convey o (brand R W a d b)) =
      WilsonIndependentMatchedOrbitReading.insert (placed R W Y a d o b) := by
  funext t v _
  have hp: translate o (orbLift v ∘ around Y.F.p.side) =
      expandAt (wrap Y.F.p.side o) (Orb.liftLinks v) := by
    funext e
    change Orb.liftLinks v (wrap Y.F.p.side (e.1+o),e.2)=
      Orb.liftLinks v (wrap Y.F.p.side e.1+wrap Y.F.p.side o,e.2)
    rw [map_add]
  change ((sectionAt R W a d).evaluate (Pi.single b 1) _).re=_
  rw [hp]
  rfl

end YM.Integration.WilsonIndependentRawNamedStencil
