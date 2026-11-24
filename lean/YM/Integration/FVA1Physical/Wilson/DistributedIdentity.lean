import YM.Integration.FVA1Physical.Wilson.DistributedScores
import YM.Integration.FVA1Physical.Wilson.AllOrdersSchur

/-! The root-localized conditional coefficients for a full boundary derivative
are the ordered jets of the independently pushed Wilson action, evaluated
in the stationary coordinates of the very same measured transition. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MeasureTheory Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Duel MSbar.Bout MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Bakery.Film MSbar.Rolling MSbar.Midpoint
open PhysicalNext.Repeat.Legato Push.Uniform Pressure RGComparison.Core16 Next.SectorChange
open Comparison.RG02 Push PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested FVA2.CityHistory
open scoped Classical Topology
variable {G : Gauge}

theorem stationary_point (A:Mosaic.Issue G) (branch:A.S.patch.Branches A.S.kernel G)
    (prem:Premier (Rolling.main A.f A.pre.clip A.pre.path))
    (crit:Critical A.F A.pre.clip A.pre.path A.ρ) (pd:(mold A.pre A.F A.v).PosDef)
    (z:Positions (Primary A.c G)) :
    bulkPoint A z = Rolling.throne A.F A.ρ (A.fClock⁻¹•z) := by
  have hc : bulkCoordinate A z = center A.F A.ρ z := by
    rw [Rolling.lovely A.F A.v A.pre.path A.pre.clip A.ρ branch prem crit z pd]
    rfl
  change meetVar (A.fClock⁻¹•z) (A.fClock⁻¹•bulkCoordinate A z)=
    meetVar (A.fClock⁻¹•z) (center A.F A.ρ (A.fClock⁻¹•z))
  rw [hc,map_smul]

theorem bulk_score_dictionary (A:Mosaic.Issue G) (χ:ChartRatio G) (hχ:LocalRatio χ)
    (branch:A.S.patch.Branches A.S.kernel G)
    (prem:Premier (Rolling.main A.f A.pre.clip A.pre.path))
    (crit:Critical A.F A.pre.clip A.pre.path A.ρ)
    (output:ClassicalMatch A.F A.pre.clip A.post.clip A.pre.path A.post.path A.ρ)
    (pd:(mold A.pre A.F A.v).PosDef) (kind:Kind A.T)
    (z:Positions (Primary A.c G)) (ℓ:List (Primary A.c G)) (p:ℕ) :
    Lap p (Duel.fire (song A.F A.v A.pre.path A.pre.clip χ A.T A.ρ)
      (MSbar.Wave.ink A.c A.post.clip A.post.path) (A.fClock⁻¹•z) ℓ)
      (bulkColumn A χ z (Duel.readScore (Duel.hands A.F G) (Duel.stampD A.F A.v G)
        (barbed A.F A.v χ A.T) ℓ) p) := by
  rw [Duel.hand A.F A.v χ A.T hχ kind]
  unfold bulkColumn
  rw [stationary_point A branch prem crit pd z]
  exact Spruce.fiscal (p:=p) A.F A.pre A.v χ (A.fClock⁻¹•z) A.post.path A.post.clip A.ρ A.T ℓ
    kind crit output hχ pd prem branch

theorem scene_score_dictionary {C:Family G} (L:Bulk.Chain C.path) {N n j k r:ℕ} {e:G.Color}
    {S:Scene C.path.levels n r} (scene:Realized L.kin N n k r e S)
    (hj:j<N) (lo:k≤j) (branch:(C.path.levels.clock.op j n).patch.Branches (C.path.levels.clock.op j n).kernel G)
    (F:Forest (C.path.levels.clock.op j n).ratio) (v:(C.path.levels.clock.op j n).Choices) :
    let A:=sceneIssue (N:=N) L S F v
    ∀ (z:Positions (Primary A.c G)) (ℓ:List (Primary A.c G)) (p:ℕ),
    Lap p (Duel.fire (song A.F A.v A.pre.path A.pre.clip L.O A.T A.ρ)
      (MSbar.Wave.ink A.c A.post.clip A.post.path) (A.fClock⁻¹•z) ℓ)
      (bulkColumn A L.O z (Duel.readScore (Duel.hands A.F G) (Duel.stampD A.F A.v G)
        (barbed A.F A.v L.O A.T) ℓ) p) := by
  intro A z ℓ p
  have trend:=(scene.budget (j+1) hj (lo.trans (Nat.le_succ _))).1
  have pd:=blueprint F v (L.kin.path N (j+1)) (C.path.levels.params (j+1)).clip branch trend.quiet
    (L.post.price _) (L.planned.gap N j n hj F)
  have clipf:=L.clips N n (j+1) hj
  have clipc:=L.clips N n j hj.le
  have pathf:=L.selected N n (j+1) hj
  have pathc:=L.selected N n j hj.le
  apply bulk_score_dictionary A L.O L.receipt branch
  · change Premier (Rolling.main _ (C.path.rep N n (j+1)).clip (C.path.rep N n (j+1)).path)
    rw [clipf,pathf]; exact trend.quiet
  · change Critical F (C.path.rep N n (j+1)).clip (C.path.rep N n (j+1)).path _
    rw [clipf,pathf]; exact (L.planned.critical N j n hj F).1
  · change ClassicalMatch F (C.path.rep N n (j+1)).clip (C.path.rep N n j).clip
      (C.path.rep N n (j+1)).path (C.path.rep N n j).path _
    rw [clipf,clipc,pathf,pathc]; exact L.planned.classicalPart N j n hj F
  · change (Push.Uniform.block (priced F v (C.path.rep N n (j+1)).clip (C.path.rep N n (j+1)).path) 0).PosDef
    rw [clipf,pathf]; exact pd
  · exact trend.bond

end YM.Integration.FVA1Physical.Wilson
