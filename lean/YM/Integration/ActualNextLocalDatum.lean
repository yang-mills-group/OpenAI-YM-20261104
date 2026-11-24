import YM.Integration.FullQLocalNumericStepData
import YM.Tree.Pines

/-! The next local datum on the same family and Census.
The next forest is native to its own original block. The previous output
roots and addresses are only transported through the stated level equality;
the next coarse roots and addresses use the original parent map. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualNextLocalDatum
open Lattice Wilson RG Marker
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open scoped Classical

variable {G : Gauge}

def forest (C : Family G) (m period : Nat) :
    Tree.Forest (C.path.levels.clock.op m period).ratio :=
  Classical.choice (Tree.select _ (C.path.levels.clock.op m period).patch.odd_side)

theorem forest_root (C : Family G) (m period : Nat)
    (x : Site (C.side (m + 1) period)) :
    stop x ((forest C m period).hike x) =
      (C.path.levels.clock.op m period).ratio.embed
        ((C.path.levels.clock.op m period).ratio.parent x) :=
  (forest C m period).hike_root x

variable {C : Family G} {V : Type} [DecidableEq V] {Gamma : Census V}

/-- The cutoff, physical period and family are unchanged. The supplied
colors and external field are retained literally at the next level. -/
def descend (D : LocalFormal.Datum C Gamma) {m : Nat} (hm : D.level = m + 1)
    (W : Comparison.RG02.Bulk.Colors Gamma G (C.side (m + 1) D.period))
    (x : Exterior.fieldDir G (C.side m D.period) 1) : LocalFormal.Datum C Gamma where
  cutoff := D.cutoff
  period := D.period
  level := m
  below := by have := D.below; omega
  forest := forest C m D.period
  tag := Classical.arbitrary _
  colors := W
  field := x

theorem descend_fields (D : LocalFormal.Datum C Gamma) {m : Nat}
    (hm : D.level = m + 1)
    (W : Comparison.RG02.Bulk.Colors Gamma G (C.side (m + 1) D.period))
    (x : Exterior.fieldDir G (C.side m D.period) 1) :
    (descend D hm W x).cutoff = D.cutoff ∧
      (descend D hm W x).period = D.period ∧
      (descend D hm W x).level = m ∧
      (descend D hm W x).colors = W ∧
      (descend D hm W x).field = x := ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem cast_mem {C : Family G} {period n n' : Nat} (h : n = n')
    (x : Site (C.side n period)) (s : Support (C.side n period)) (hx : x ∈ s) :
    cast (congrArg (fun k => Site (C.side k period)) h) x ∈
      cast (congrArg (fun k => Support (C.side k period)) h) s := by
  subst n'
  exact hx

section Roots
variable [Fintype V] {J : Request V} {A : NumericSchedule C J}
    {D : LocalFormal.Datum C Gamma} (F : AnalyticInput J A D)

theorem output_roots_mem (v : V) : F.coarseRoots v ∈ F.outputAddresses v := by
  exact Finset.mem_image.mpr ⟨F.fineRoots v, F.input_origins v, F.roots v⟩

variable {m : Nat} (hm : D.level = m + 1)

/-- Only the lattice index is transported; these are the old output roots. -/
def fineRoots : V → Site (C.side (m + 1) D.period) := fun v =>
  cast (congrArg (fun k => Site (C.side k D.period)) hm) (F.coarseRoots v)

def fineAddresses : V → Support (C.side (m + 1) D.period) := fun v =>
  cast (congrArg (fun k => Support (C.side k D.period)) hm) (F.outputAddresses v)

def coarseRoots : V → Site (C.side m D.period) := fun v =>
  (C.path.levels.clock.op m D.period).ratio.parent (fineRoots F hm v)

def coarseAddresses : V → Support (C.side m D.period) := fun v =>
  (fineAddresses F hm v).image (C.path.levels.clock.op m D.period).ratio.parent

theorem fine_roots_mem (v : V) : fineRoots F hm v ∈ fineAddresses F hm v :=
  cast_mem hm (F.coarseRoots v) (F.outputAddresses v) (output_roots_mem F v)

theorem roots (v : V) :
    (C.path.levels.clock.op m D.period).ratio.parent (fineRoots F hm v) =
      coarseRoots F hm v := rfl

theorem coarse_roots_mem (v : V) : coarseRoots F hm v ∈ coarseAddresses F hm v := by
  exact Finset.mem_image.mpr ⟨fineRoots F hm v, fine_roots_mem F hm v, rfl⟩

end Roots
end YM.Integration.ActualNextLocalDatum
end
