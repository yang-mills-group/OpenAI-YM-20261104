import YM.QuadraticLocal.Fk.Capsule
/-! # Finite ordinary presentations and synthetic roots

These are made from the incoming Rows, periodized and complete unmasked
values. `colors` reuses `Bulk` with the extra native step action supplied by
`Fk.grant`; `fkStandard` etc. Lit basis singular powers synchronized with
interaction sums, via one weight function on the true marker tests. Don't
assume this is the same as the `Pulse` query in the projection of analytic
kernels until proving equality.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Haiku.Coat AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration AllOrder.Catch AllOrder.Catch.Clock AllOrder.Floe AllOrder.Plateau
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {V:Type}{G:Gauge} {n c:Side} {k j d r:ℕ} {a b σ :ℝ}
open Aperture Poetry Echo Work.G05 Toggle Aux Aux.Name Marker Multi
open QuadraticLocal.Sunrise
variable {ι α : Type} [DecidableEq V] {P:Passport n V} {R:Census V}
variable (M:ι→ Row P R G α)
variable (F: Finset ι) (L:Layout G) (T:Finset Age)
namespace ScatterR
set_option quotPrecheck false
local notation "R₀"=> Focus.census ι
open Comparison.RG02
open Marker Multi
-- ℝ colors are powered mark functions for Fk, have denominator.
section mix
variable {V₁:Type} [DecidableEq V₁](J:Census V₁)(e:ι→Multi.Hot J)(q:ι→ℂ) (w:V₁→ℕ)
local notation "Yₐ"=> Launch.index J w

def colors : Bulk.Colors J G n:= Fk.grant L T { vac:=0,power i:= (Launch.index J w i.val)+1, mark i t:= ∑ j∈ F.filter (fun j:ι=> i.val=(e j).val), (q j • (fun v=> (↑(Loan.letter ((M j).lamp) (M j).atom (M j).center t v) :ℂ))) }
local notation "Pℓ"=> ScatterR.colors M F L T J e q w
local notation "E₀"=> (Progress.Command.Common) -- unused

def familyAt (i:ι)(d:ℝ) : Config G n→ ℂ:= fun v=> q i * Complex.ofReal ( Loan.letter ((M i).lamp) (M i).atom (M i).center d v)
local notation "Oℓ"=> familyAt M q
lemma markEq (i:Multi.Hot J) : (Pℓ).mark i=∑ j∈ F.filter (fun j:ι=> i.val=(e j).val), ScatterR.familyAt M q j:= by
 funext f g; unfold colors; simp only [Fk.grant, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]; rfl -- defeq
lemma mature (j:ι): Assembly.GradeAt ((M j).lamp.power) (Bulk.projected (ScatterR.familyAt M q j)) := ((Loan.frame ((M j).lamp) (M j).atom (M j).center).linear_contact (q j • Complex.ofRealCLM)).lower (Nat.le_add_right _ _)
include w
-- mixing: arbitrary q & h.K.Clock.Of.
variable (H:∀ i∈F,(M i).lamp.toll= Launch.index J w (e i).val)
include H
lemma standard (ht:Legal T L): (ScatterR.colors M F L T J e q w).Standard:= by
 apply Fk.standard L T ht
 · intro i; let f:= Pℓ; change Assembly.GradeAt (f.power i) (Bulk.projected (f.mark i)); rw [show f.mark i= ∑ j∈ F.filter (fun j:ι=> i.val=(e j).val), ScatterR.familyAt M q j from ScatterR.markEq M F L T J e q w i]; unfold Bulk.projected; simp_rw [Finset.sum_apply]; apply Assembly.GradeAt.list_sum; intro j hj; obtain ⟨hp,hπ⟩:=Finset.mem_filter.mp hj; rw [show f.power i=(M j).lamp.power from congr_arg (·+1) ((congr_arg (Yₐ) hπ).trans (H j hp).symm)]; exact mature M q j -- args
 · intro i t g U; change ((Pℓ).mark i t (gauge g U))=_; rw [ScatterR.markEq]; change _ = (Pℓ).mark i _ _; rw [ScatterR.markEq]; simp_rw [Finset.sum_apply]; exact Finset.sum_congr rfl fun j _=> congr_arg (fun p:ℝ=> q j * Complex.ofReal p) (Loan.natural _ _ _ t (M j).lawful g U)
 intro i t; have he:Continuous ((Pℓ).mark i t) := by
      change Continuous (fun x=> (Pℓ).mark i t x); simp_rw [ScatterR.markEq,Finset.sum_apply]; apply continuous_finsetSum; intro i _; exact continuous_const.mul (Complex.continuous_ofReal.comp (Loan.conti (M i|>.lamp) _ _ t)) -- name
 obtain ⟨c₀,h⟩:= isCompact_univ.exists_bound_of_continuousOn he.continuousOn; exact ⟨he.measurable,c₀,fun z=>h z (Set.mem_univ _)⟩
omit H
-- pulse via Balcony displayC with σ map. Need EXACT extensional across entire `J`, including those with zero wanted.
variable [DecidableEq ι][Fintype ι]
variable (S:Ratio c n)(t₀ : ι→ Site c) (Y' : ι → Site c→ Site n)(hY:∀ i,Y' i (t₀ i)=(M i).center)
include hY
omit [DecidableEq ι] in
lemma cursor : Balcony.feed J (fun i=>(M i).lamp) (fun i=>(M i).atom) Y' L T (Bunch.mapC t₀) w e q= ScatterR.colors M univ L T J e q w:= by
     let extC (V Y : Bulk.Colors J G n)(hv:V.vac=Y.vac)(hw:V.power=Y.power)(he:V.mark=Y.mark): V=Y:=by cases V; cases Y; congr
     refine extC _ _ rfl rfl ?_; funext j z v
     rw [markEq]; unfold Balcony.feed Fk.grant Balcony.feedM; simp_rw [Finset.sum_apply]; apply Finset.sum_congr rfl; intro i hi; rw [Finset.sum_eq_single_of_mem (t₀ i) (Finset.mem_univ _)]; unfold familyAt Balcony.pigment Bunch.mapC; rw [hY]; simp [mul_comm]; intro a h hn; unfold Balcony.pigment Bunch.mapC; simp [hn]
end mix
-- useful when restrict-retain, reindex roots
section actual
open Comparison.RG02
variable [DecidableEq ι][Fintype ι]
def edition := ScatterR.colors M F L T (Focus.census ι) Focus.detailI 1 (fun i=> (M i).lamp.toll)
local notation "W"=> edition M F L T
lemma standard_issue (he: Legal T L) : Bulk.Colors.Standard (W) := standard M F L T _ _ _ _ (fun i _=> (Focus.weight (fun i:ι=>(M i).lamp.toll) i).symm) he
end actual
abbrev birth (C: Club M) : Bulk.Colors (Focus.census (Club.Keys M C)) G n:= by
    exact ScatterR.edition (Club.troops M C) univ L T
end ScatterR
end YM.QuadraticLocal.Earn

