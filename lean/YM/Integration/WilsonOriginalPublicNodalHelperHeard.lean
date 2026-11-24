import YM.Integration.WilsonOriginalPublicNodalHelperElection
import YM.Integration.WilsonOriginalPublicNodalTwinOrbit

/-! The physical-prefix and the grouped helper are commissioned with the same original kernel and unmarked book. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalHelperHeard
open Lattice RG RG.Supply Org Input PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open Source Labels PertExtension RegulatorIR.Epoch RegulatorIR.Epoch.League
open XSpace Precision RegulatorIR RegulatorIR.Oracle RegulatorIR.Atlas RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open RegulatorIR.Taping RegulatorIR.Uniform RegulatorIR.Calibration RegulatorIR.FVAAlt2 RegulatorIR.Momentum
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.AuxPlates Next.Foundations
open WilsonOriginalPublicNodalHelperShape (length physical)
open WilsonOriginalPublicNodalCommonRaw (Court)
open scoped Classical ENNReal NNReal
variable {G:Gauge}{H:Hol G}(R:PhysicalNext.Repeat.Legato.Run G)(P:Master H)(chart:ChartRatio G)(V:XSpace.Run)
    (e h k tier extra:ℕ)(p b u:ℕ)(γ:ℝ)(lo:0<γ)(hi:γ<1)
variable (Z:∀P:Patch,P.Branches R.family.path.levels.clock.kernel G)(col:G.ColorIndex)
    (B:WilsonIndependentEvenPassport.Menu P chart R.family.path.levels.clock.kernel V e h k tier extra)
    (late:5≤tier){X:Type}(m j:X → ℕ)(w:X → ℕ → ℕ)
    (blocks:∀x t,(R.family.S.block (m x+t)).val=V.ratio^(w x t))(r:X → ℕ)(ap:X → ℝ)(pos:∀x,0≤ap x)




open RegulatorIR.Halo RegulatorIR.Prim RegulatorIR.Profiles RegulatorIR.Binding RegulatorIR.Geometry RegulatorIR.Cluster RegulatorIR.Budget RegulatorIR.Motion XSpace.Rose XSpace.Cirrus
open WilsonIndependentRawRosterBudget (span)
open WilsonOriginalPublicNodalCommonRaw (value raw fee prior)
open WilsonOriginalPublicNodalTwinOrbit (stride lift)
open WilsonOriginalPublicNodalHelperElection (TwoNotebooks)
open WilsonOriginalPublicNodalPhysicalHelper (period sample)
variable (T:TwoNotebooks R P chart V e h k tier extra p b u γ Z col B late m j w blocks r ap pos)
    (i:X → ℕ)(H:ℝ)
local notation "A" => WilsonOriginalPublicNodalHelperElection.groupedCourt R P chart V e h k tier extra p b u γ Z col B late m j w blocks r ap pos T
local notation "C" => WilsonOriginalPublicNodalHelperElection.physicalCourt R P chart V e h k tier extra p b u γ Z col B late m j w blocks r ap pos T i H

theorem original {I:Type}(W:Initialize G)(σ:I → Bool)(d:I → ℕ)
    (key:∀i,(R.family.labels.level (d i)).Index)(arms:Composite I)
    (mesh:X → ℝ)(hm:∀x,0 < mesh x)(lay:X → Fin 2 → Cover)(origin:X → Room)
    (base:X → Cover)(sites:X → I → Cover)(gs:Choice (length (physical j w) r B.a))(ps:Choice j)
    (q:ℕ)(hq:q≤p)(enough:∀x,r x ≤ physical j w x)
    (room:∀x,(stride (A) (C) gs ps x:ℝ) ≤ (period V j w x).side.val/8)
    (field:∀x,span (slide 1 (base x)) (sites x) arms ≤ ap x)
    (funded:∀x,ENNReal.ofReal (1+span (slide 1 (base x)) (sites x) arms) ≤ (C).L.val x):
    let b:=fun x=>sample V j w x (mesh x) (hm x) (lay x) (origin x)
    ∃U V' F:ℝ,∃a v h':ℕ,0≤U ∧ 0≤V' ∧ 0≤F ∧ ∀n:Page ps.after.spans,
      let x:=n.bindW
      let z:=lift (A).S.P (stride (A) (C) gs ps) base sites
      let original:=value R W σ d key arms (A) sites (gs.choose x) q
      let returned:=value R W σ d key arms (C) sites (ps.after.page n) q
      ‖original-raw R W σ d key arms (b x) (z x) q‖ ≤ fee (A) U a gs x ∧
      ‖raw R W σ d key arms (b x) (z x) q-returned‖ ≤ fee (C) V' v ps x+prior (C) F h' ps x ∧
      ‖original-returned‖ ≤ fee (A) U a gs x+(fee (C) V' v ps x+prior (C) F h' ps x):=by
  intro b
  have sideA (x:X):TopF (A).n x=(b x).F.p.side:=(WilsonOriginalPublicNodalPhysicalHelper.sides V j w r B.a enough x).2
  have sideB (x:X):TopF (C).n x=(b x).F.p.side:=rfl
  have measure (x:X):(A).S.P x=((period V j w x).side.val:ℝ):=congrArg (fun s:Side=>(s.val:ℝ)) (sideA x)
  apply WilsonOriginalPublicNodalTwinOrbit.original R W σ d key arms (A) (C) b base sites gs ps
    (fun x=>Nat.zero_le _) (fun x=>Nat.zero_le _) q hq sideA sideB measure
    (fun x=>by rw [measure];exact room x) _ funded
  intro x
  exact (ENNReal.ofReal_le_ofReal (add_le_add_right (field x) 1)).trans (le_add_right le_rfl)

end YM.Integration.WilsonOriginalPublicNodalHelperHeard
end
