import YM.Integration.WilsonOriginalPublicNodalStandardReturn
import YM.Integration.WilsonOriginalPublicNodalSignedClock

/-! The physical finite quadrature at the fitted dose and original report clock. The physical-prefix payroll here starts from the flat bare K top. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalStandardCells
open Lattice RG RG.Supply Org Input PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open Source Labels PertExtension RegulatorIR.Epoch RegulatorIR.Epoch.League
open XSpace Precision RegulatorIR RegulatorIR.Oracle RegulatorIR.Atlas RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open RegulatorIR.Taping RegulatorIR.Uniform RegulatorIR.Calibration RegulatorIR.FVAAlt2 RegulatorIR.Momentum
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.AuxPlates Next.Foundations
open WilsonOriginalPublicNodalHelperShape (length physical)
open WilsonOriginalPublicNodalCommonRaw (Court)
open scoped Classical ENNReal NNReal BigOperators PowerSeries
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


open WilsonThermometerPositionTunedSlope (Columns)
open WilsonIndependentPublicReportComplex (row)
structure Allowance where
  first:ℝ≥0
  second:ℝ≥0
  old:ℝ≥0
  a:ℕ
  v:ℕ
  h:ℕ

variable {I:Type}[Fintype I](W:Initialize G)(σ:I → Bool)(d:I → ℕ)(arms:Composite I)
    (mesh:X → ℝ)(hm:∀x,0 < mesh x)(lay:X → Fin 2 → Cover)(origin:X → Room)
    (base:X → Cover)(sites:X → I → Cover)(gs:Choice (length (physical j w) r B.a))(ps:Choice j)
    (request:X → Requests B.a)(at₀:X → Choice (M V B.a))
    (residue:∀x,(request x).val%B.a=r x)(ages:∀x,(at₀ x).age (request x)=gs.age x)
    (enough:∀x,r x ≤ physical j w x)


def earlier (a:Columns R d)(n:Page ps.after.spans):PowerSeries ℂ:=
  PowerSeries.mk fun q=>value R W σ d a arms (C) sites (ps.after.page n) q

def sampled (a:Columns R d)(x:X):PowerSeries ℂ:=
  PowerSeries.mk fun q=>(note ((report R W σ d a arms ((S₀).payroll (Y₀) G Z (sheet F₀))
    (fun _=>sites x)).main ((at₀ x).choose (request x)) q 0):ℂ)

def bill (L:Allowance)(x:X):ℝ:=
  fee (A) L.first L.a gs x+(fee (C) L.second L.v ps x+prior (C) L.old L.h ps x)

local notation "source" => sampled R P chart V e h k tier extra Z B late F₀ W σ d arms sites request at₀
local notation "sink" => earlier R P chart V e h k tier extra p b u γ Z col B late m j w blocks r ap pos T i H W σ d arms sites ps
local notation "charge" => bill R P chart V e h k tier extra p b u γ Z col B late m j w blocks r ap pos T i H gs ps
include book hm lay origin residue ages enough in
omit [Fintype I] in
theorem entry
    (room:∀x,(stride (A) (C) gs ps x:ℝ) ≤ (period V j w x).side.val/8)
    (field:∀x,span (slide 1 (base x)) (sites x) arms ≤ ap x)
    (funded:∀x,ENNReal.ofReal (1+span (slide 1 (base x)) (sites x) arms) ≤ (C).L.val x)
    (a:Columns R d)(l:ℕ):∃L:Allowance,∀n:Page ps.after.spans,
  ‖PowerSeries.coeff (min l p) (source a n.bindW)-PowerSeries.coeff (min l p) (sink a n)‖≤charge L n.bindW:=by
  have receipts:=WilsonOriginalPublicNodalStandardReturn.original R P chart V
    e h k tier extra p b u γ Z col B late m j w blocks r ap pos T i H F₀ book W σ d a arms mesh hm lay
    origin base sites gs ps request at₀ residue ages (min l p) (min_le_right l p) enough room field funded
  dsimp only at receipts
  rcases receipts with ⟨U,V',F,a',v,h',hU,hV,hF,atStop⟩
  refine ⟨⟨⟨U,hU⟩,⟨V',hV⟩,⟨F,hF⟩,a',v,h'⟩,?_⟩
  intro n
  simp only [sampled,earlier,PowerSeries.coeff_mk]
  exact (atStop n).2.2

include book hm lay origin residue ages enough in
theorem original
    (room:∀x,(stride (A) (C) gs ps x:ℝ) ≤ (period V j w x).side.val/8)
    (field:∀x,span (slide 1 (base x)) (sites x) arms ≤ ap x)
    (funded:∀x,ENNReal.ofReal (1+span (slide 1 (base x)) (sites x) arms) ≤ (C).L.val x):∃L:Columns R d → ℕ → Allowance,
    ∀(D q:ℕ),q≤p → ∀(Cell:Type)[Fintype Cell](ear:Cell → Page ps.after.spans)(ν:Cell → ℂ)
      (v:Cell → ∀t,(R.family.labels.level (d t)).Coeff),
      let K:=fun z=>F₀ (WilsonIndependentExactPlate.report V B.a (request (ear z).bindW))
      let c:=fun z (a:Columns R d)=>∏t,v z t (a t)
      ‖∑z,ν z*(PowerSeries.coeff q (WilsonIndependentPublicReportComplex.apply (K z) D
           (∑a,PowerSeries.C (c z a)*source a (ear z).bindW))-
         PowerSeries.coeff q (WilsonIndependentPublicReportComplex.apply (K z) D
           (∑a,PowerSeries.C (c z a)*sink a (ear z))))‖≤
        ∑z,‖ν z‖*(∑a,‖c z a‖*∑l∈Finset.range (q+1),charge (L a l) (ear z).bindW*‖row (K z) D q l‖):=by
  classical
  let issued:=entry R P chart V e h k tier extra p b u γ Z col B late m j w blocks r ap pos T i H F₀ book
    W σ d arms mesh hm lay origin base sites gs ps request at₀ residue ages enough room field funded
  choose L stock using issued
  refine ⟨L,?_⟩
  intro D q hq Cell _ ear ν v K c
  apply WilsonOriginalPublicNodalSignedClock.test K D q ν c
  intro z a l hl
  have use:=stock a l (ear z)
  rwa [min_eq_left (hl.trans hq)] at use

end YM.Integration.WilsonOriginalPublicNodalStandardCells
end
