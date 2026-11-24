import YM.Integration.WilsonIndependentRawNamedStencil
import YM.RegulatorIR.Profiles.Trek

/-! Report for both actual section choices on the conventional inversion
board. The occupied two-source row has its own connected contractions. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentRawNamedProduct
open Lattice RG Source Labels PertExtension Orb XSpace XSpace.Rose XSpace.Cirrus
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Halo
open RegulatorIR.Profiles RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.Step RegulatorIR.Prim RegulatorIR.Cluster RegulatorIR.Diagram
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Taping
open WilsonIndependentRawNamedStencil WilsonIndependentMatchedNamedPair
open scoped Classical

variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
local notation "F" d:max => R.family.labels.level d
variable (a c:Bool)(d e:ℕ)(b:(R.family.labels.level d).Index)(b':(R.family.labels.level e).Index)

def word (o z:Cover) : Portrait G :=
  convey o (brand R W a d b) * convey z (brand R W c e b')

def ranks (o z:Cover) : Orders (Foot G) := accord (shifted R W a d b o) (shifted R W c e b' z)

theorem united (o z:Cover) :
    let m:=((F d).grades b).2+((F e).grades b').2
    BasisT m m (word R W a c d e b b' o z) (ranks R W a c d e b b' o z) ∧
      Ranks m (ranks R W a c d e b b' o z) := by
  intro m
  have l:=named R W a d b o
  have r:=named R W c e b' z
  exact ⟨Profiles.BasisT.united l.1 r.1 l.2 r.2,rank_pair l.2 r.2⟩

variable {I:Type}{M:I→ℕ}{n:Page M→Side}{S:Heir n G}

def report (T:S.Accounts)(o z:I → Cover) : T.Report (((F d).grades b).2+((F e).grades b').2) :=
  declaring T (fun i=>ranks R W a c d e b b' (o i) (z i))
    (fun i=>(united R W a c d e b b' (o i) (z i)).2)

theorem opening (T:S.Accounts)(o z:I → Cover)(i:I) :
    let m:=((F d).grades b).2+((F e).grades b').2
    BasisT m m (word R W a c d e b b' (o i) (z i))
      ((report R W a c d e b b' T o z).main (Page.opening M i)) :=
  (united R W a c d e b b' (o i) (z i)).1

theorem hearing (Y:Sample 2)(o z:Cover)(q:ℕ) :
    PowerSeries.coeff q (Bare.normalized (W.tree Y.F.p) G
      (printed R W Y a d o b * printed R W Y c e z b')) =
      (plotPT WilsonIndependentMatchedOrbitReading.originalClock
        (vital Y.F.p.side (word R W a c d e b b' o z))
        (((F d).grades b).2+((F e).grades b').2) q:ℂ) := by
  rw [pair]
  congr 2
  funext t v h
  have l:=congrFun (congrFun (congrFun (submitted R W a d b o Y) t) v) h
  have r:=congrFun (congrFun (congrFun (submitted R W c e b' z Y) t) v) h
  exact congrArg₂ (·*·) l.symm r.symm

end YM.Integration.WilsonIndependentRawNamedProduct
