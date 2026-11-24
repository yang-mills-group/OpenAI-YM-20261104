import YM.Integration.FVA1Physical.Wilson.SceneTop

/-! Discharge both analytic comparisons at the first stored (non-bare)
vacuum on the actual run. The realized scene can choose its own forest and
bits, while the independent Wilson input can use other admitted choices. -/
noncomputable section

namespace YM.Integration.RunFormalChain
open Lattice RG RG.Supply Precision Input Org Extra.Histories
variable {G : Gauge} {M : Metals G} {P : Rolls M.p} {A : Alloy M P}
/-- Formal coefficients for any chosen physical Bolt, even when the surrounding
trajectory was selected by the marked C18 construction. -/
def fromBolt (T : Bolt A) : Comparison.RG02.Bulk.Chain (Issue.trail T) where
  preCosts := M.p
  lengths := P
  post := A.post
  horizon := A.B.M
  O := M.O
  receipt := A.B.ratio
  kin := A.B.kin
  planned := A.B.support
  selected N p m hm := ((T.sticks N p).prices m (Nat.zero_le _) hm).1.path.trans
    (congrArg (fun f => f N m) A.B.bases)
  clips N p m hm := ((T.sticks N p).prices m (Nat.zero_le _) hm).1.clip

@[simp] theorem fromBolt_of_run (R : PhysicalNext.Repeat.Legato.Run G) :
    fromBolt R.T = fromRun R := rfl
end YM.Integration.RunFormalChain

namespace YM.Integration.FVA1Physical.Wilson

open RG Lattice YM.Wilson Exterior Tree Marker PhysicalNext.Repeat.Legato Comparison.RG02
open MSbar MSbar.Rolling MSbar.Wave MSbar.Midpoint Push Push.Uniform Precision
open FormalOPE.RG10.InversionTop
open scoped Classical Matrix.Norms.Frobenius

variable {G : Gauge} {C : Family G} (L : Bulk.Chain C.path) (physical : C.Makes)
    (stencils : ∀ d, Bid.pop (C.localSection d)) {j p k r : ℕ} {e : G.Color}
    {S : Scene C.path.levels p r}

include physical stencils

/-- Full unreset vacuum matching at every perturbative order through the
scene demand, at every coarse field and for physical marked input data.
The scene's own reset and kinetic subtraction are shown explicitly. -/
theorem first_vacuum_on_chain (hS : Realized L.kin (j+1) p k r e S)
    (hk : k ≤ j) (large : Bid.Larger (G := G) (C.path.levels.clock.op j p)) :
    let P := L.kin.path (j+1) j
    let Q := L.kin.path (j+1) (j+1)
    let c := C.side j p
    let clip := (C.path.levels.params j).clip
    ∃ (B : Forest (C.path.levels.clock.op j p).ratio) (u : (C.path.levels.clock.op j p).Choices),
      let Z := colorCut B u Q (C.path.levels.params (j+1)).clip L.O (S.Poly (j+1))
        (L.kin.stationary (j+1) j p B)
      S.Poly j = bley (S.action j) Z (ink c clip P) ∧
      ∀ (I : Type) [DecidableEq I] [Fintype I] (R : Census I) (d : ℕ)
        (U : I → Stamp.Reservation C (C.side (j+1) p) d),
      ∀ (F : Forest (C.path.levels.clock.op j p).ratio) (v : (C.path.levels.clock.op j p).Choices)
        (x : Positions (Primary c G)) (i : ℕ), i ≤ r →
        let D := MSMatch.SourceTop.datum R j p U F v (tint G _ x)
        Lis.atlas Z r i P clip x =
          (D.vacuumAction L r i (tint G _ x)).re - (D.vacuumAction L r i 0).re := by
  let a := C.path.levels
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
  intro I _ _ R d U F v x i hi
  let D := MSMatch.SourceTop.datum R j p U F v (tint G _ x)
  have hW : Bare.Witnessed D.colors (D.kernel L) :=
    MSMatch.SourceTop.witnessed L R j p U physical stencils
  exact first_scene_identification (D.kernel L) D.colors F v r (a.budget J) hW hpre x hi

end YM.Integration.FVA1Physical.Wilson
