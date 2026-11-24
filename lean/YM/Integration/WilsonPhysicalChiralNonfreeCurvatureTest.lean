import YM.Integration.WilsonPhysicalChiralNonfreeNominatedVote
import YM.X.Try.Hub

/-! Polarization uses three constant closed curvature assignments on the same
physical filed vector. The measured absolute error is taken after the signs. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalChiralNonfreeCurvatureTest
open Finset Filter Function RG Labels RG05Readout.Address Wilson Source Lattice
open Next.Rank Next.Rank.Price Next.Rank.Atlas Next.Rank.Station Next.UVStress
open Further.CorrectedLift Cells Extraction Table Climb Trace Trace.Pilot MergeProof.East
open PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonPositionCapTransport WilsonMaxwellThermometerNominatedOrientation WilsonMaxwellThermometerMaximalHead
open WilsonMeasuredPublicEntranceGridDebit WilsonOriginalMicroscopicGuardedPage Pert.Asymptotics
open Trace.Physical Push.RelayDifference Bandage
open Spec OPE OPE.Orbits RG17 PhysMS PhysMS.Frame Maxwell XSpace XSpace.Normalize
open scoped Classical BigOperators Topology
variable {G:Gauge}{d:ℕ}

def chart (X:Fin 3→PositionX.Tri.PanelL G)(S:Finset (Fin 3)): Labels.Taylor G 0:=
  (PositionX.Tri.τφ (∑ i∈S,X i)).choose

theorem curvature (X:Fin 3→PositionX.Tri.PanelL G)(S:Finset (Fin 3)):
    PositionX.Tri.curτ (chart X S)=∑ i∈S,X i:=(PositionX.Tri.τφ _).choose_spec

def ear (F:Labels.Frame G d)(X:Fin 3→PositionX.Tri.PanelL G)(i:F.Index):ℂ:=
  ∑ S:Finset (Fin 3), (-1:ℂ)^(3-S.card) * Labels.read (PositionX.Tri.chunk (chart X S)) (F.basis i).val

def reading (F:Labels.Frame G d)(X:Fin 3→PositionX.Tri.PanelL G)(x:F.Coeff):ℂ:=
  ∑ i:F.Index, if F.grades i=(d,d/2) then ear F X i*x i else 0

def wage (F:Labels.Frame G d)(X:Fin 3→PositionX.Tri.PanelL G):ℝ:=∑ i:F.Index,‖ear F X i‖

theorem tested (F:Labels.Frame G d)(X:Fin 3→PositionX.Tri.PanelL G)(χ:ℝ)(x p:F.Coeff):
    ‖(χ:ℂ)*reading F X x-reading F X p‖≤wage F X*error F χ x p:=by
  unfold reading error
  rw [mul_sum,←sum_sub_distrib,mul_sum]
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro i _
  by_cases h:F.grades i=(d,d/2)
  · simp only [if_pos h]
    rw [show (χ:ℂ)*(ear F X i*x i)-ear F X i*p i=ear F X i*((χ:ℂ)*x i-p i) by ring,norm_mul]
    exact mul_le_mul_of_nonneg_right (single_le_sum (fun j _=>norm_nonneg (ear F X j)) (mem_univ i)) (norm_nonneg _)
  · simp only [if_neg h,mul_zero,sub_zero,norm_zero,le_refl]

variable (R:Run G){f:Extraction.Order}{l:Ultrafilter (ℕ×ℕ)}
    {H:(Bel R.family.book).Hierarchy}{S:Table R.family.book}
local notation "C"=>R.family

theorem original (simple:G.Simple)(A:ℝ→Group C 6)(T:ℝ→tower S)
    (book:Book (f:=f) (l:=l) (H:=H) A T){ε:ℝ}(pos:0<ε):
    ∀ᶠ r in trail,∀ᶠ z:Cutoffs in f.fuse,∀s (i:Fin 3),
    let V:=A r; let d:=index V (grade i); let k:=V.station.k
    let v:=source C s i; let y:=V.station.wheel.atCut z d (V.change (grade i) v)
    let F:=(C).labels.level d; let χ:=(shrink C k z.1 z.2)^(d.val/2)/(Station.mag (C).path.levels V.station.b k)^d.val
    let a:=(((C).S.a k:ℂ)^d.val)⁻¹
    R.t d≤k → (C).ref d≤k → 1≤((C).path.levels.budget k).supportExponent →
    ∀U:(C).label d≃ₗ[ℂ](C).label d,∀X:Fin 3→PositionX.Tri.PanelL G,
    ‖(χ:ℂ)*reading F X (a • U (U.symm (fitted R d k z.1 z.2 y)))-reading F X (ladder C d v)‖≤
      wage F X*ε:=by
  filter_upwards [WilsonPhysicalChiralNonfreeNominatedVote.reported R simple A T book pos] with r native
  filter_upwards [native] with z given
  intro s i V d k v y F χ a date ref width U X
  exact (tested F X χ _ _).trans (mul_le_mul_of_nonneg_left (given s i date ref width U).le
    (Finset.sum_nonneg fun _ _=>norm_nonneg _))

end YM.Integration.WilsonPhysicalChiralNonfreeCurvatureTest
