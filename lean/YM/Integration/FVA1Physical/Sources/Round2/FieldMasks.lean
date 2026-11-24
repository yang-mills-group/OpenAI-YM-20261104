import YM.Integration.FVA1Physical.Sources.Round2.FieldRealized

/-! All squarefree marker sectors use one physical trajectory, one realized forest
and its bits, one coarse background, and the same vacuum normalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Finset MSbar.Heath YM.Integration.FVA1Physical.Wilson YM.Integration Exterior Tree
open Qlocal.Schedule RGComparison.Core16.Spool YM.MSbar Push.Uniform
open MSbar.Midpoint MSbar.Rolling MSbar.Whisk Pressure
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open scoped Topology BigOperators Classical
variable {G : Gauge}

variable {κ:Type} [Fintype κ]

private theorem shrinkInvoice {a b:Goal G} (buy:Obtainable a)
    (f:∀ M D A X,a M D A X → b M D A X) : Obtainable b := by
  intro s T C z R E hdr
  obtain ⟨g,first⟩:=buy s T C z R E hdr
  refine ⟨g,?_⟩
  intro l hl D w v Z F S pocket records admissible P menu wait
  obtain ⟨W,hw,price⟩:=first l hl D w v Z F S pocket records admissible P menu wait
  refine ⟨W,hw,?_⟩
  intro Y hY cost bar W' priced B archive shape alloy exchange η q d m h j hf hv hh ha
  exact f _ _ _ _ (price Y hY cost bar W' priced B archive shape exchange η q d m h j hf hv hh ha)

/-- All receipts on a finite nonempty list can be bought on a single physical Run.
The individual receipts may specify different independent Wilson coefficient banks. -/
theorem finiteInvoice {I:Type} [Fintype I] [Nonempty I] (H:I→Goal G) (buy:∀ i,Obtainable (H i)) :
    Obtainable (fun M D A X=>∀ i,H i M D A X) := by
  classical
  have partialBuy (S:Finset I): Obtainable (fun M D A X=>∀ i∈S,H i M D A X) := by
    induction S using Finset.induction_on with
    | empty => apply shrinkInvoice (buy (Classical.choice (inferInstance:Nonempty I))); simp
    | @insert i S hi ih =>
      apply shrinkInvoice ((buy i).also ih)
      intro M D A X h t mt
      rcases Finset.mem_insert.mp mt with eq|mem
      · simpa only [eq] using h.1
      · exact h.2 t mem
  exact shrinkInvoice (partialBuy Finset.univ) fun _ _ _ _ h t=>h t (mem_univ t)

def maskInvoice (u:G.ColorIndex) (V:Voice G) (J:κ→Lamp G) : Goal G :=
  fun M D A X=>∀ t:Finset κ,fieldInvoice u V (fun i:t=>J i.1) M D A X

theorem maskInvoice_obtainable (hG:G.Simple) (u:G.ColorIndex) (V:Voice G) (cle:Clear G V)
    (J:κ→Lamp G) : Obtainable (maskInvoice u V J) :=
  finiteInvoice (fun t:Finset κ=>fieldInvoice u V (fun i:t=>J i.1))
    (fun t=>fieldInvoice_obtainable hG u V cle (fun i:t=>J i.1))

set_option maxHeartbeats 2000000 in
/-- Repeated actual comparison for every masked source on precisely the same
realized Wilson bank, including the empty vacuum sector. -/
theorem all_mask_ports_on (J:κ→Lamp G) (hG:G.Simple) (R:PhysicalNext.Repeat.Legato.Run G)
    (u:G.ColorIndex) (V:Voice G) (mask:maskInvoice u V J R.metals R.rolls R.alloy R.kit)
    (invoice:Qlocal.Schedule.vacuumInvoice u V R.metals R.rolls R.alloy R.kit) :
    ∀ p s m L:ℕ, 6 ≤ s → 4 ≤ m → p+2 ≤ m →
      ∀ᶠ k:ℕ in atTop,∀ N n, k ≤ N →
        (∃ S:Scene R.family.path.levels n p, Realized R.alloy.B.kin N n k p (Lis.sun G u) S) ∧
        ∀ (S:Scene R.family.path.levels n p) (scene:Realized R.alloy.B.kin N n k p (Lis.sun G u) S),
        ∀ (j:ℕ) (kj:k ≤ j) (jN:j < N),
          let F:=(scene.step j jN kj).choose
          let v:=(scene.step j jN kj).choose_spec.choose
          let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S F v
          let x:=R.family.path.levels.clock.hatBeta j
          let y:=R.family.path.levels.clock.hatBeta (j+1)
          S.Poly j=A.Zpost R.metals.O ∧ ∀ (z:Site A.f) (Z:Positions (Primary A.c G)), ‖Z‖ ≤ Mosaic.hull x →
            ∀ (t:Finset κ) (part:Bool),FieldPort A R.metals.O V p L (fun i:t=>J i.1) part y (y^Mosaic.pawn p) z Z := by
  intro p s m L hs hm hr
  let terms:= (Finset.univ : Finset (Finset κ))
  have passes (t:Finset κ):=actual_field_ports_pinned_on (fun i:t=>J i.1) hG R u V (mask t) invoice p s m L hs hm hr
  filter_upwards [terms.eventually_all.mpr (fun t _=>passes t)] with k passed N n kn
  have empty:=(passed ∅ (mem_univ _) N n kn)
  refine ⟨empty.1,?_⟩
  intro S scene j kj jN
  refine ⟨(empty.2 S scene j kj jN).1,?_⟩
  intro z Z norm t part
  exact ((passed t (mem_univ _) N n kn).2 S scene j kj jN).2 z Z norm part

end YM.Integration.FVA1Physical.Round2.Curvature
