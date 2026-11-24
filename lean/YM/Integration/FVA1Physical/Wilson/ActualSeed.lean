import YM.Integration.FVA1Physical.Wilson.ActualOrbit

/-! A single actually inserted physical stencil, with independent source placements, has a bounded continuous true multi-block conditional and an exact native signed representative at every earlier boundary. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset MeasureTheory Lattice RG RG.Supply YM.Wilson Source Labels Precision Input Org Extra.Histories
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato ThroughLaunch Roof Push.PriceCompiler
open UVNext.CouplingReset Next.Foundations Graces Roost LocalLTE LocalLTE.Vinca LocalLTE.Concourse
open MergeProof Planned.GuardedAtom Planned.GuardedAtom.Guard Push Push.Local Push.AbsoluteSums
open RGComparison.Core16.Spool GapsR2RG GapsR2RG.Anchor MSbar MSbar.Bulk MSbar.Mosaic
open Tree MSbar.Midpoint
open YM.Integration.FVA1Physical.Wilson YM.Integration.FVA1Physical.Marked
open scoped Classical BigOperators Topology
variable {G:Gauge}

open YM.Integration.FVA1Physical.Round2.Curvature MSbar.Heath.Cottage
open scoped BigOperators

variable (R:PhysicalNext.Repeat.Legato.Run G)
local notation "H" => R.family.path
local notation "F0" => (frames G).level 0
local notation "D0" => localSection G 0

theorem true_tape_bound {N n u:ℕ} (cut:u ≤ N) {B:ℝ}
    (φ:Config G (R.family.side u n) → ℝ) (mφ:Continuous φ) (cap:∀ U,|φ U| ≤ B)
    (j:ℕ) (hj:j ≤ u) : Continuous (haarTape R N n u φ j hj) ∧ ∀ U,|haarTape R N n u φ j hj U| ≤ B := by
  induction hj using Nat.decreasingInduction with
  | self => rw [haarTape_top];exact ⟨mφ,cap⟩
  | of_succ j hj ih =>
    rw [haarTape_step R φ hj]
    let A:=(H).rep N n (j+1);let K:=(H).levels.clock.op j n;let ψ:=haarTape R N n u φ (j+1) hj
    have density:=A.envelope (R.makes.wilson.represents N n (j+1) (show j+1 ≤ N by omega)).good
    have env:Envelope ψ:=⟨ih.1.measurable,B,ih.2⟩
    have pos (W):0 < K.push A.beta A.eval W :=
      (SectorNext.Vacuum.strictly H R.makes.wilson N n j (hj.le.trans cut) W).trans_eq
        (congrFun (R.makes.wilson.steps N n j (hj.trans_le cut)).1 W)
    have br:K.patch.Branches K.kernel G:=((H).levels.blocks j n).branches
    constructor
    · exact (Progress.DirectedRecipe.continuous_push K A.beta br (ψ*A.eval) ((env.mul density).integrable _)).div
        (Progress.DirectedRecipe.continuous_push K A.beta br A.eval (density.integrable _)) (fun W=>(pos W).ne')
    intro W
    have adm:Admitted W A K _ _ _ _ _:=⟨(R.makes.wilson.represents N n (j+1) (show j+1 ≤ N by omega)).good,
      fun U=>(SectorNext.Vacuum.strictly H R.makes.wilson N n (j+1) (show j+1 ≤ N by omega) U).le,pos W,
      (H).levels.transition_mass j n A.beta⟩
    have lo:=nn W adm env (Envelope.const (-B)) (fun U=>(abs_le.mp (ih.2 U)).1)
    have hi:=nn W adm (Envelope.const B) env (fun U=>(abs_le.mp (ih.2 U)).2)
    rw [e_const W adm] at lo hi
    exact abs_le.mpr ⟨lo,hi⟩

theorem physical_wallet_tape (simple:G.Simple) {N n u:ℕ} (fine:u<N) (start:R.t 0 ≤ u)
    {I:Type} [Fintype I] {d:ℕ} (a:I → CoverLabel G d) (ready:∀ i,R.t (a i).1.val ≤ u+1)
    (b:Site (R.family.side (u+1) n)) (o:I → Site (R.family.side (u+1) n)) (part:Bool) (rad:ℕ)
    (placed:∀ i,separation (o i-b) 0 ≤ rad) (j:ℕ) (hj:j ≤ u) (early:R.t 0 ≤ j) :
    let S:=(H).levels.clock.op u n;let F:=(H).rep N n (u+1)
    let z:=anchorTape R n u (S.ratio.parent b) j hj
    let φ:=fun U=>look part (tally (freshLamps a) o U)
    let ψ:=haarTape R N n u (fun W=>expect S F W φ) j hj
    let Q₀:=(H).rep N n j;let M:=fiberRate R j u*measuredBirth R a N n u b o part rad
    ∃ Q:Coefficient F0 (R.family.side j n), Q.Format z (hol G) Q₀ ∧ Q.remBound z Q₀ (kappa H j) M ∧
        Q.density z D0 Q₀=(fun W=>(Q₀.eval W:ℂ)*(ψ W:ℂ)) ∧
        (∀ W,(ψ W:ℂ)=Q.exponentialEntry z D0 Q₀ W+forcedShare Q Q₀ W) := by
  intro S F z φ ψ Q₀ M
  let A:=(H).rep N n u
  obtain ⟨P,shape,dens,bill⟩:=current_run_field R simple fine start a ready b o part rad placed
  let root:=S.ratio.parent b
  have paid: P.remBound root A (kappa H u) (measuredBirth R a N n u b o part rad):=bill
  have iden (W:Config G (R.family.side u n)):(expect S F W φ:ℂ)=P.exponentialEntry root D0 A W+forcedShare P A W:=
    current_all_boundaries H R.makes.wilson fine root φ P dens W
  apply transported_wallet R simple fine.le P root _ (fun W=>expect S F W φ) shape paid _ j hj early
  funext W
  have pos:=SectorNext.Vacuum.strictly H R.makes.wilson N n u fine.le W
  have eq: P.density root D0 A W/(A.eval W:ℂ)=(expect S F W φ:ℂ):=
    (normalized_entry P A root D0 W pos).trans (iden W).symm
  rw [mul_comm];exact (div_eq_iff (Complex.ofReal_ne_zero.mpr pos.ne')).mp eq

end YM.Integration.FVA1Physical.Wilson
