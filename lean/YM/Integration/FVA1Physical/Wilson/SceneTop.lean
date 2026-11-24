import YM.Integration.FVA1Physical.Wilson.SceneFirst

/-! Discharge both analytic comparisons at the first stored (non-bare)
vacuum on the actual run. The realized scene can choose its own forest and
bits, while the independent Wilson input can use other admitted choices. -/
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson

open RG Lattice YM.Wilson Exterior Tree Marker PhysicalNext.Repeat.Legato Comparison.RG02
open MSbar MSbar.Rolling MSbar.Wave MSbar.Midpoint Push Push.Uniform Precision
open FormalOPE.RG10.InversionTop
open scoped Classical Matrix.Norms.Frobenius

variable {G : Gauge} (A : Run G) {j p k r d : ℕ} {e : G.Color}
    {S : Scene A.family.path.levels p r} {V : Type} [DecidableEq V] [Fintype V]
    (R : Census V) (U : V → Stamp.Reservation A.family (A.family.side (j+1) p) d)

/-- Full unreset vacuum matching at every perturbative order through the
scene demand, at every coarse field and for physical marked input data.
The scene's own reset and kinetic subtraction are shown explicitly. -/
theorem first_purchased_vacuum (hS : Realized (RunFormalChain.fromRun A).kin (j+1) p k r e S)
    (hk : k ≤ j) (large : Bid.Larger (G := G) (A.family.path.levels.clock.op j p)) :
    let L := RunFormalChain.fromRun A
    let P := L.kin.path (j+1) j
    let Q := L.kin.path (j+1) (j+1)
    let c := A.family.side j p
    let clip := (A.family.path.levels.params j).clip
    ∃ (B : Forest (A.family.path.levels.clock.op j p).ratio) (u : (A.family.path.levels.clock.op j p).Choices),
      let Z := colorCut B u Q (A.family.path.levels.params (j+1)).clip L.O (S.Poly (j+1))
        (L.kin.stationary (j+1) j p B)
      S.Poly j = bley (S.action j) Z (ink c clip P) ∧
      ∀ (F : Forest (A.family.path.levels.clock.op j p).ratio) (v : (A.family.path.levels.clock.op j p).Choices)
        (x : Positions (Primary c G)) (i : ℕ), i ≤ r →
        let D := MSMatch.SourceTop.datum R j p U F v (tint G _ x)
        Lis.atlas Z r i P clip x =
          (D.vacuumAction L r i (tint G _ x)).re - (D.vacuumAction L r i 0).re := by
  let L := RunFormalChain.fromRun A
  let a := A.family.path.levels
  let Q := L.kin.path (j+1) (j+1)
  let P := L.kin.path (j+1) j
  let clip := (a.params j).clip
  let clip' := (a.params (j+1)).clip
  let J := j+1
  have hj : j < J := Nat.lt_succ_self _
  obtain ⟨B,u,_,_,out⟩ := hS.step j hj hk
  let ρ := L.kin.stationary J j p B
  let Z := colorCut B u Q clip' L.O (S.Poly J) ρ
  have hfin : Trend (S.film J) (S.Poly J) Q clip' r :=
    (hS.budget J le_rfl (hk.trans hj.le)).1
  have serves : Serves (a.clock.op j p) G :=
    ⟨large.1,(a.blocks j p).symmetric,(a.blocks j p).gauge,large⟩
  have pos := blueprint B u Q clip' large.1 hfin.quiet (L.post.price _)
    (L.planned.gap J j p hj B)
  have hpre : Trend (shunt (a.clock.op j p) (S.film J)) Z P clip r :=
    newT B u Q P clip' clip ρ L.O L.receipt (S.Poly J) (S.film J) r serves
      (L.planned.critical J j p hj B).1 (L.planned.classicalPart J j p hj B) hfin pos
  have top : S.film J = breed G (a.S.side J p) := hS.top0
  rw [top] at hpre
  refine ⟨B,u,out,?_⟩
  intro F v x i hi
  let D := MSMatch.SourceTop.datum R j p U F v (tint G _ x)
  have hW : Bare.Witnessed D.colors (D.kernel L) :=
    MSMatch.SourceTop.witnessed L R j p U A.makes (fun s => Next.Foundations.valuation G s)
  exact first_scene_identification (D.kernel L) D.colors F v r (a.budget J) hW hpre x hi

end YM.Integration.FVA1Physical.Wilson
