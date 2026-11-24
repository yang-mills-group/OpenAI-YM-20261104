import YM.Integration.FVA1Physical.Round2.ProgramPinnacle
import YM.Integration.FVA1Physical.Round2.VacuumInvoice

/-! Uniform operator geometry and the one-step vacuum analytic inputs for the actual C18 exit. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Round2
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent

open YM.Qlocal.Schedule
/-- Purchase the operator size needed at every scale and period before selecting the circuit. -/
def coarseRoom : Goal G := fun _ D A _ => ∀ i, snows D i ≤ A.delay.shells i

theorem coarseRoom_obtainable : Obtainable (coarseRoom (G := G)) := by
  intro s T C z R E hdr
  refine ⟨fun _ => 0, ?_⟩
  intro l hl D w v Z F S pocket records admissible P menu V
  let W : Delays P := {V with shells := fun i => max (V.shells i) (snows D i)}
  refine ⟨W, ⟨le_rfl,le_rfl,fun i => le_max_left ..,le_rfl⟩, ?_⟩
  intro Y hY cost bar W' price B archive shape exchange η q b bt guide J hf hv hw ha div i
  exact (le_max_right ..).trans (hY.shells i)

variable {M : Metals G} {P : Rolls M.p} {A : Alloy M P} {X : Factor A}
    {C : ℕ → ℝ} {K : Bid.Worth} {T : Bolt A} {l : ℕ}
    (g : Bandage.Harmonics X C K T l)
    (room : coarseRoom M P A X)

include room in
theorem circuit_merit : YM.MSbar.Alto.Merit A.B.a A.B.M := by
  refine ⟨?_,fun n m hm p => X.pledging.conducts.full n m _ hm⟩
  intro m p
  let a := A.B.a
  let S := a.clock.op m p
  let j := a.clock.J (m+1)
  have vol := A.B.valid.volume m p
  have h₁ : A.delay.shells j ≤ (a.S.side m p).val :=
    (Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)).trans vol
  refine ⟨(a.blocks m p).branches,?_,?_⟩
  · have h : Pressure.macroR S.patch = (j+7)*(a.S.block m).val := by
      change (j+3)*(a.S.block m).val + 4*(a.S.block m).val = _
      ring
    change 100 * Pressure.macroR S.patch ≤ _
    rw [h, Extra.Iteration.block_eq A.B.valid, ← Nat.mul_assoc]
    exact ((room j).trans h₁).trans (by rw [S.sizes]; exact Nat.le_mul_of_pos_right _ S.patch.L.pos)
  · change _ < (a.clock.schedule.side m p).val
    have h := a.fits.sizeT m p
    omega

include g in
theorem circuit_decent (j : ℕ) : WilsonStartup.Decent (A.B.a.params j).clip (A.B.a.budget j) := by
  let t := g.port (j+1) j 0 (Nat.lt_succ_self _)
  exact (X.machine.passes (Nat.lt_succ_self j) t.career.turns).1.decent

include g in
theorem circuit_psalm (N m n : ℕ) (h : m < N) :
    let a := A.B.a
    let i := a.clock.J (m+1)
    let j := a.clock.J m
    let β := a.clock.hatBeta m
    let target := X.target i j
    YM.MSbar.Bulk.Psalm (a.clock.op m n) ((Issue.trail T).rep N n (m+1)) (a.clock.threshold m)
      ((target.goal (P.L i) β)⁻¹ * Real.exp (-(target.mark (P.L i) (X.shape.μ i j) β))) := by
  let u := g.port N m n h
  obtain ⟨spring, _⟩ := u.drink h
  dsimp only
  rw [g.charged N m n h]
  exact Mallow.Many.atSpring h spring ⟨0,Set.left_mem_Icc.mpr le_rfl⟩ g.tag.r

end YM.PhysicalNext.Repeat.Legato.Round2
