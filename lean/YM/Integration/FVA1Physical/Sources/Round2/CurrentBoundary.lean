import YM.Integration.FVA1Physical.Marked.CurrentRunSpatial
import YM.Integration.FVA1Physical.Sources.Round2.TwoPhysicalFields
import YM.Integration.FVA1Physical.Wilson.SceneReadout

/-! The normalized conditional measurement of a genuinely inserted mixed field
on an arbitrary retained boundary. This formula retains every signed forced
owner on configurations with distant failed plaquettes. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Finset MeasureTheory Lattice RG RG.Supply YM.Wilson Source Labels Precision Input Org Extra.Histories
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato ThroughLaunch Roof Push.PriceCompiler
open UVNext.CouplingReset Next.Foundations Graces Roost LocalLTE LocalLTE.Vinca LocalLTE.Concourse
open MergeProof Planned.GuardedAtom Planned.GuardedAtom.Guard Push Push.Local Push.AbsoluteSums
open RGComparison.Core16.Spool GapsR2RG GapsR2RG.Anchor MSbar MSbar.Bulk MSbar.Mosaic
open Tree MSbar.Midpoint
open YM.Integration.FVA1Physical.Wilson YM.Integration.FVA1Physical.Marked
open scoped Classical BigOperators Topology
variable {G:Gauge}

/-- Signed total over every admissible polymer inventory divided by the true gas. -/
def forcedShare {d:ℕ} {F:Frame G d} {n:Side} (Q:Coefficient F n) (R:Rep G n) (U:Config G n) : ℂ :=
  (∑' b,Q.marked R b U)/(R.activities.gas R.p U:ℂ)

theorem normalized_entry {d:ℕ} {F:Frame G d} {n:Side} (Q:Coefficient F n)
    (R:Rep G n) (z:Site n) (C:SectionData F) (U:Config G n) (positive:0 < R.eval U) :
    Q.density z C R U/(R.eval U:ℂ)=Q.exponentialEntry z C R U+forcedShare Q R U := by
  have h:(R.eval U:ℂ)=(Real.exp (R.exponent U):ℂ)*(R.activities.gas R.p U:ℂ):=Complex.ofReal_mul _ _
  have e:(Real.exp (R.exponent U):ℂ)≠0:=Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have g:(R.activities.gas R.p U:ℂ)≠0:=by
    intro zero
    apply Complex.ofReal_ne_zero.mpr positive.ne'
    rw [h,zero,mul_zero]
  unfold Coefficient.density forcedShare
  rw [h]
  field_simp [e,g]

variable (H:History G) (sel:H.Selected) {N n m:ℕ} (hm:m < N)
local notation "RI" => H.rep N n (m+1)
local notation "RO" => H.rep N n m
local notation "K" => H.levels.clock.op m n
local notation "D0" => localSection G 0
include sel hm in
theorem current_all_boundaries (z:Site (H.S.side m n))
    (f:Config G (H.S.side (m+1) n) → ℝ) (Q:Coefficient ((frames G).level 0) (H.S.side m n))
    (exactness:Q.density z D0 RO=(K).push (RI).beta (fun W=>((RI).eval W:ℂ)*(f W:ℂ))) (U:Config G (H.S.side m n)) :
    (expect K RI U f:ℂ)=Q.exponentialEntry z D0 RO U+forcedShare Q RO U := by
  have denominator : (RO).eval U=(K).push (RI).beta (RI).eval U:=congrFun (sel.steps N n m hm).1 U
  have cast : (K).push (RI).beta (fun W=>((RI).eval W:ℂ)*(f W:ℂ)) U=(((K).push (RI).beta (f*(RI).eval) U:ℝ):ℂ) := by
    unfold StepData.push
    simp only [Pi.mul_apply,Complex.real_smul,←Complex.ofReal_mul,smul_eq_mul]
    simp_rw [mul_comm ((RI).eval _) (f _)]
    exact integral_complex_ofReal
  rw [MSbar.Bulk.expect,←denominator,Complex.ofReal_div,←cast,←congrFun exactness U]
  exact normalized_entry Q RO z D0 U (SectorNext.Vacuum.strictly H sel N n m hm.le U)

/-- The change of conditional measure caused by an entirely arbitrary exterior
is given by differences of a single purchased coefficient's regular and forced
parts. Its cost is the true marked birth cost on the fixed physical trajectory. -/
theorem current_exterior_owners {I:Type} [Fintype I] {d r:ℕ} (R:PhysicalNext.Repeat.Legato.Run G)
    (simple:G.Simple) (hm:m < N) (start:R.t 0 ≤ m)
    (a:I → CoverLabel G d) (ready:∀ j,R.t (a j).1.val ≤ m+1)
    (y:Site (R.family.side (m+1) n)) (o:I → Site (R.family.side (m+1) n)) (part:Bool)
    (radius:ℕ) (foot:∀ j,separation (o j-y) 0 ≤ radius) :
    let H:=R.family.path
    let B:=H.rep N n m
    let T:=H.levels.clock.op m n
    let z:=T.ratio.parent y
    let v:=fun i=>o i-y
    let cost:=Doors.rate (H.S.block m)*birthCost (H.rep N n (m+1)).p (lampSupport a v) (H.levels.clock.forcedAllowance (m+1))
      (localFieldTariff (H.rep N n (m+1)).p a (R.alloy.B.a.params (m+1)).columns radius+
        ‖(look part (tally (freshLamps a) v 1):ℂ)‖) (2*stencilBound (freshLamps a))
    ∃ Q:Coefficient ((frames G).level 0) (R.family.side m n), Q.Format z (hol G) B ∧
      Q.remBound z B (kappa H m) cost ∧
      ∀ (C:Scene H.levels n r) (F:Forest T.ratio) (bits:T.Choices),
        let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) C F bits
        ∀ (U W:Config G A.c), (externalScores (freshLamps a) A o part U W:ℂ)=
          (Q.exponentialEntry z D0 B U-Q.exponentialEntry z D0 B W)+(forcedShare Q B U-forcedShare Q B W) := by
  intro H' B T z v cost
  obtain ⟨Q,form,dens,price⟩:=current_run_field R simple hm start a ready y o part radius foot
  refine ⟨Q,form,price,?_⟩
  intro C F bits A U W
  let φ:= fun P=>look part (tally (freshLamps a) o P)
  have branch:T.patch.Branches T.kernel G := (H'.levels.blocks m n).branches
  have pos (P): 0 < T.push A.pre.beta A.pre.eval P :=
    (SectorNext.Vacuum.strictly H' R.makes.wilson N n m hm.le P).trans_eq (congrFun (R.makes.wilson.steps N n m hm).1 P)
  have changeMeasure:=retained_covariance T branch A.pre U W φ (pos U) (pos W)
  change (externalScores (freshLamps a) A o part U W:ℂ)=_
  have formula (P:Config G A.c) : (expect T A.pre P φ:ℂ)=Q.exponentialEntry z D0 B P+forcedShare Q B P :=
    current_all_boundaries H' R.makes.wilson hm z φ Q dens P
  rw [show externalScores (freshLamps a) A o part U W=expect T A.pre U φ-expect T A.pre W φ from changeMeasure.symm,
    Complex.ofReal_sub,formula U,formula W]
  ring

end YM.Integration.FVA1Physical.Round2.Curvature
