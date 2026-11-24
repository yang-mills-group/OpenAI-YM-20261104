import YM.Integration.WilsonOriginalPublicNodalHelperHeard
import YM.Integration.WilsonOriginalPublicNodalStandardPrefix
import YM.Integration.WilsonOriginalPublicNodalPrefixSale

/-! The prescribed two-length sample is evaluated at its own fitted clock. Its true stopped report crosses the safe helper and returns to the early physical page. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalStandardReturn
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


open WilsonIndependentExactPlate (Requests M S)
open WilsonIndependentRawRosterOrbit (report)
local notation "S₀" => S V B.a B.positive tier (le_trans (by decide:4 ≤ 5) late)
local notation "D₀" => WilsonOriginalPublicNodalHelperCircuit.circuit V (physical j w) r B.a tier B.positive (le_trans (by decide:4 ≤ 5) late)
local notation "Y₀" => Oracle.books R.family.path.levels.clock.kernel
variable (F₀:Tent (M V B.a))(book:Notebook (S V B.a B.positive tier (le_trans (by decide:4 ≤ 5) late)) (Oracle.books R.family.path.levels.clock.kernel) G Z col (Rocket.native _) F₀ p)

include book in
theorem original {I:Type}(W:Initialize G)(σ:I → Bool)(d:I → ℕ)
    (key:∀i,(R.family.labels.level (d i)).Index)(arms:Composite I)
    (mesh:X → ℝ)(hm:∀x,0 < mesh x)(lay:X → Fin 2 → Cover)(origin:X → Room)
    (base:X → Cover)(sites:X → I → Cover)(gs:Choice (length (physical j w) r B.a))(ps:Choice j)
    (request:X → Requests B.a)(at₀:X → Choice (M V B.a))
    (residue:∀x,(request x).val%B.a=r x)(ages:∀x,(at₀ x).age (request x)=gs.age x)
    (q:ℕ)(hq:q≤p)(enough:∀x,r x ≤ physical j w x)
    (room:∀x,(stride (A) (C) gs ps x:ℝ) ≤ (period V j w x).side.val/8)
    (field:∀x,span (slide 1 (base x)) (sites x) arms ≤ ap x)
    (funded:∀x,ENNReal.ofReal (1+span (slide 1 (base x)) (sites x) arms) ≤ (C).L.val x):
    let b:=fun x=>sample V j w x (mesh x) (hm x) (lay x) (origin x)
    ∃U V' F:ℝ,∃a v h':ℕ,0≤U ∧ 0≤V' ∧ 0≤F ∧ ∀n:Page ps.after.spans,
      let x:=n.bindW
      let z:=lift (A).S.P (stride (A) (C) gs ps) base sites
      let original:ℂ:=note ((report R W σ d key arms ((S₀).payroll (Y₀) G Z (sheet F₀))
        (fun _=>sites x)).main ((at₀ x).choose (request x)) q 0)
      let returned:=value R W σ d key arms (C) sites (ps.after.page n) q
      ‖original-raw R W σ d key arms (b x) (z x) q‖ ≤ fee (A) U a gs x ∧
      ‖raw R W σ d key arms (b x) (z x) q-returned‖ ≤ fee (C) V' v ps x+prior (C) F h' ps x ∧
      ‖original-returned‖ ≤ fee (A) U a gs x+(fee (C) V' v ps x+prior (C) F h' ps x):=by
  intro sample₀
  obtain ⟨U,V',F,a,v,h',hU,hV,hF,ear⟩:=WilsonOriginalPublicNodalHelperHeard.original R P chart V
    e h k tier extra p b u γ Z col B late m j w blocks r ap pos T i H W σ d key arms
    mesh hm lay origin base sites gs ps q hq enough room field funded
  refine ⟨U,V',F,a,v,h',hU,hV,hF,?_⟩
  intro n x z old returned
  have route:=WilsonOriginalPublicNodalStandardPrefix.route V (physical j w) r B.a tier B.positive
    (le_trans (by decide:4 ≤ 5) late) (at₀ x) gs (request x) x (ages x) (residue x)
  have entrance:=WilsonOriginalPublicNodalStandardPrefix.root V (physical j w) r B.a tier B.positive
    (le_trans (by decide:4 ≤ 5) late) (request x) x
  have change:=WilsonOriginalPublicNodalPrefixSale.scalar (S₀) (D₀) (at₀ x) gs (request x) x route
    entrance (Y₀) Z col F₀ T.F' book T.fresh R W σ d key arms (fun _=>sites x) sites rfl q hq
  have same:old=value R W σ d key arms (A) sites (gs.choose x) q:=congrArg (fun a:ℝ=>(a:ℂ)) change
  rw [same]
  exact ear n

end YM.Integration.WilsonOriginalPublicNodalStandardReturn
end
