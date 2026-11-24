import YM.Integration.WilsonOriginalPublicTrialPhaseTrace
import YM.Integration.WilsonReportingGuardedSource
import YM.MergeProof.Fondue
import YM.MergeProof.Wicket
import YM.OPE.Replicas.Apiary

/-! An uncut fitted arm is born on the occupied addresses of the inherited
law. Its positive guard supplement and its rooted hard profile share an owner. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseBirth
open Finset Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Guard Push Local RelayDifference.Opening Next.Foundations
open MergeProof MergeProof.Accent PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open OPE.Therm Push.AbsoluteSums.Animals Extra.Multi
open WilsonPositionProgramBlockedTrialAddBack
open scoped Classical BigOperators ContDiff
variable {G:Gauge} (R:Run G)
private theorem zero_derivs {n:Side} (l:List (Directions G n)) (U:Config G n) :
    leftDerivs (0:Config G n→ℂ) l U=0:=by
  induction l generalizing U with
  | nil => rfl
  | cons A l ih => simp only [leftDerivs,ih,deriv_const]

private theorem zero_regular {n:Side} (P:BudgetPoint)(D:Support n) : P.Regular D (0:Config G n→ℂ):=by
  refine ⟨fun _ _ _=>rfl,measurable_const,fun _ _=>rfl,fun _ _=>contDiffAt_const,?_⟩
  intro U h A l hl
  simpa only [zero_derivs] using (hasDerivAt_const (0:ℝ) (0:ℂ))

private theorem zero_bound {n:Side} (P:BudgetPoint)(D:Support n)(o:Site n):P.supBounds o D (0:Config G n→ℂ) 0:=by
  refine ⟨le_rfl,fun _ _ _ _ _=>?_⟩
  simp [zero_derivs]

private theorem zero_vanish {n:Side}(H:Hol G)(d:ℕ)(o:Site n):H.PiVanish d o (0:Config G n→ℂ):=by
  intro J
  refine ⟨contDiffAt_const,fun j _=>?_⟩
  change iteratedDeriv j (fun _:ℝ=>(0:ℂ)) 0=0
  simp

variable {K N per:ℕ} {T:Campaign R} (book:Campaign.Pillars R T)
local notation "C" => R.family
local notation "P" => (C).path.rep N per K

include book in
theorem original (live:K≤N)(d:ℕ)(o:Site ((C).side K per))(v:(C).label d)
    (small:((((C).localSection d).footprint o).card:ℝ) * (C).path.levels.clock.forcedAllowance K≤1):
    let F:=(C).labels.level d
    let S:=(C).localSection d
    let D:=S.footprint o
    let κ:=(C).path.levels.clock.forcedAllowance K
    let M:=BasisCost.price S * F.coeffSize (names R d N per K v)
    ∃ q:Coefficient F ((C).side K per),q.x=v ∧ q.Format o (C).params (P) ∧
      (∀U,q.density o S (P) U=((P).eval U:ℂ)*uncut R d N per K o v U) ∧
      q.remBound o (P) (Real.sqrt κ) ((P).p.mass D 0 + 2*(D.card:ℝ)*Real.sqrt κ*(P).p.mass D M) ∧
      ∃ ψ,Attainment (P).p o ψ (reservedMass (P).p D M) ∧
        profile (P).activities q.forced=hook (P).activities (P).p.threshold ψ:=by
  intro F S D κ M
  let f:=S.places (names R d N per K v) o
  let tail:=f-masked (P).p.threshold D f
  have root:o∈D:=by
    exact Finset.mem_image.mpr ⟨0,(R.makes.sections d).anchored,by simp⟩
  have site:=S.placed_local o (names R d N per K v)
  have inv:=S.placed_invariant (R.makes.sections d) o (names R d N per K v)
  have bore:= (S.continuous_places (names R d N per K v) o).measurable
  have att:Attaches (P).p.threshold D tail:=by
    refine ⟨fun U V diff eq=>congrArg₂ Sub.sub (site U V diff) (uses_mask _ site U V diff eq),
      fun h U=>congrArg₂ Sub.sub (inv h U) (invariant_mask inv _ _ h U),
      bore.sub (masked_measurable _ _ _ bore),?_⟩
    intro U healthy
    simp [tail,masked_eq _ _ _ _ healthy]
  have bound (U):‖tail U‖≤M:=by
    by_cases ok:Healthy (P).p.threshold D U
    · simp [tail,masked_eq _ _ _ _ ok]
      exact (norm_nonneg _).trans (BasisCost.full S (names R d N per K v) o U)
    · simpa only [tail,Pi.sub_apply,masked_ne _ _ _ _ ok,sub_zero] using BasisCost.full S (names R d N per K v) o U
  have board:=(R.makes.wilson.represents N per K live).good
  let key:=Guard.Keeper.sufficient ((book.yields N per).slots K (Nat.zero_le _) live)
  apply platter (P) key (C).params S board (forcedPos (C).path.levels K) small (zero_regular _ _) (zero_bound _ _ _) rfl
    (fun _=>zero_vanish _ _ _) root att ((norm_nonneg _).trans (bound 1)) bound
  intro U
  change (v 0+masked (P).p.threshold D f U)+masked (P).p.threshold D (0:Config G ((C).side K per)→ℂ) U+
    (f U-masked (P).p.threshold D f U)=v 0+f U
  by_cases ok:Healthy (P).p.threshold D U
  · simp [masked_eq _ _ _ _ ok]
  · simp [masked_ne _ _ _ _ ok]

end YM.Integration.WilsonOriginalPublicTrialPhaseBirth
