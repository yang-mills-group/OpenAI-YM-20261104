import YM.Integration.FVA1Physical.Wilson.FluctuationOn

/-! Mixed physical stencil readings at every non-bare step on one construction.
The cutoffs precede the torus and independent placements. The forest used
for every field comparison is also the one producing the realized outgoing
vacuum polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Finset Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open PhysicalNext.Repeat.Legato Cub Circlet Graces Roost Qlocal.Schedule
open YM.Integration.FVA1Physical.Wilson RGComparison.Core16.Spool MSbar MSbar.Heath MSbar.Heath.Stock
open MSbar.Midpoint
open Tree Pressure Push.Uniform Exterior
open scoped Classical Topology BigOperators
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι→Lamp G)

/-- Obtain the field-specific analytic threshold and the native physical good-sector
certificate simultaneously for every admissible subset of marks. -/
def maskFluctuationInvoice (u:G.ColorIndex) (V:Voice G) (cle:Clear G V) (hG:G.Simple) : Goal G :=
  fun M D A X=>∀ t:Finset ι, fluctuationInvoice (fun i:t=>J i.1) V cle hG M D A X ∧
    fieldInvoice u V (fun i:t=>J i.1) M D A X

theorem maskFluctuationInvoice_obtainable (hG:G.Simple) (u:G.ColorIndex) (V:Voice G) (cle:Clear G V) :
    Obtainable (maskFluctuationInvoice J u V cle hG) :=
  finiteInvoice (fun t:Finset ι=>fun M D A X=>fluctuationInvoice (fun i:t=>J i.1) V cle hG M D A X ∧
    fieldInvoice u V (fun i:t=>J i.1) M D A X) fun t=>
    (selectedThreshold_obtainable (G:=G) (fluctuationMenu (fun i:t=>J i.1) V cle hG)).also
      (fieldInvoice_obtainable hG u V cle (fun i:t=>J i.1))

def FluctuationMaskReadings (R:PhysicalNext.Repeat.Legato.Run G) (u:G.ColorIndex) : Prop :=
      ∀ p s L : ℕ, 6 ≤ s → ∀ D η : ℝ, 0 ≤ D → 0 < η →
      ∀ᶠ k : ℕ in atTop, ∀ N n, k≤N →
        (∃ S : Scene R.family.path.levels n (p+2), Realized R.alloy.B.kin N n k (p+2) (Lis.sun G u) S) ∧
        ∀ (S : Scene R.family.path.levels n (p+2)) (scene:Realized R.alloy.B.kin N n k (p+2) (Lis.sun G u) S),
          ∀ (j:ℕ) (kj:k ≤ j) (jN:j < N),
            let F:=(scene.step j jN kj).choose
            let v:=(scene.step j jN kj).choose_spec.choose
            let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S F v
            let y:=R.family.path.levels.clock.hatBeta (j+1)
            S.Poly j=A.Zpost R.metals.O ∧ ∀ (b:Site A.f) (Z:Positions (Primary A.c G)), ‖A.fClock • Z‖ ≤ D*Heath.Cottage.room y →
              ∀ (t:Finset ι) (part:Bool), PhysicalFieldComparison (fun i:t=>J i.1) A R.metals.O y η p L part b Z

/-- The shared fixed trajectory, retained background, forest and interacting vacuum
work for both complex components of all subset insertions at once. -/
theorem fluctuation_masks_pinned_on (hG:G.Simple) (R:PhysicalNext.Repeat.Legato.Run G)
    (u:G.ColorIndex) (V:Voice G) (cle:Clear G V) (frame:R.metals.O=chart G)
    (masks:maskFluctuationInvoice J u V cle hG R.metals R.rolls R.alloy R.kit)
    (invoice:Qlocal.Schedule.vacuumInvoice u V R.metals R.rolls R.alloy R.kit) :
    FluctuationMaskReadings J R u := by
  intro p s L hs D η hD hη
  let terms:=(univ:Finset (Finset ι))
  have each (t:Finset ι):=fluctuation_pinned_on (fun i:t=>J i.1) hG R u V cle frame
    (masks t).1 (masks t).2 invoice p s L hs D η hD hη
  filter_upwards [terms.eventually_all.mpr (fun t _=>each t)] with k paid N n kn
  have empty:=paid ∅ (mem_univ _) N n kn
  refine ⟨empty.1,?_⟩
  intro S scene j kj jN
  refine ⟨(empty.2 S scene j kj jN).1,?_⟩
  intro b Z norm t part
  exact ((paid t (mem_univ _) N n kn).2 S scene j kj jN).2 b Z norm part

theorem fluctuation_mask_trajectory {goal : Goal G} (extra : Obtainable goal) (hG : G.Simple)
    (penalty : ℝ) (positive : 0 < penalty) :
    ∃ (R:PhysicalNext.Repeat.Legato.Run G) (u:G.ColorIndex) (V:Voice G),
      R.family.path.levels.clock.kernel.penalty=penalty ∧ goal R.metals R.rolls R.alloy R.kit ∧
      R.metals.O=chart G ∧ Clear G V ∧ Docket R.family u R.metals.O R.alloy.B.M R.alloy.B.kin ∧
      FluctuationMaskReadings J R u := by
  haveI:=hG.nontrivial_color
  have dim : 0<G.lieDim := by rw [Gauge.lieDim,←G.colorIso.finrank_eq];exact Module.finrank_pos
  let u:G.ColorIndex:=⟨0,dim⟩
  obtain ⟨V,cle⟩:=MSbar.Heath.vocals G
  let proposal:=((extra.also fixedWilsonChart_obtainable).also
    (maskFluctuationInvoice_obtainable J hG u V cle)).also (vacuumInvoice_obtainable hG u V cle)
  obtain ⟨R,pen,⟨⟨⟨grant,frame⟩,masks⟩,invoice⟩⟩:=Run.rampK hG proposal penalty positive
  obtain ⟨docket,_⟩:=docket_of_invoice hG R u V invoice
  exact ⟨R,u,V,pen,grant,frame,cle,docket,fluctuation_masks_pinned_on J hG R u V cle frame masks invoice⟩


end YM.Integration.FVA1Physical.Round2.Curvature
