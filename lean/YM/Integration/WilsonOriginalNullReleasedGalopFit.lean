import YM.Integration.WilsonOriginalNullReleasedMaximalLimit
import YM.Integration.WilsonMaxwellThermometerSignedWallet

noncomputable section
namespace YM.Integration.WilsonOriginalNullReleasedGalopFit
open Function Filter Finset RG Lattice Wilson Source Labels Next.Rank Next.Rank.Price Next.Rank.Atlas
open Next.Rank.Station Further.CorrectedLift Cells Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open Spec OPE OPE.Orbits RG17 PhysMS PhysMS.Frame Maxwell XSpace XSpace.Normalize WilsonPositionCapTransport
open WilsonMaxwellThermometerMaximalHead WilsonMaxwellThermometerChargedHeads WilsonMaxwellThermometerSignedWallet
open WilsonOriginalThermometerPalette WilsonOriginalNullReleasedMaximalLimit
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "C₀"=>R.family
local notation "road"=>R.family.path.levels

open WilsonMaxwellThermometerNominatedOrientation
/-- One actual charged maximal coordinate of the public signed tensor is dominated by its total table. -/
theorem entry (A:Group C₀ 6)(r:ℝ)(v:∀i,Axes R i)(i:Fin 3)
    (j:((C₀).labels.level (grade i)).Index):
    dist (maximalPaid R r v i j) (maxpart R (target R) i j) ≤ sumError R A r univ v:=by
  let F:=(C₀).labels.level (grade i)
  let u:=ladder C₀ (grade i) (source C₀ univ i)
  let f:=fun j:F.Index=>if F.grades j=(levels i,levels i/2) then
    ‖(((r^(levels i))⁻¹:ℝ):ℂ)*v i j-u j‖ else 0
  have good:∀j,0≤f j:=fun j=>by dsimp only [f];split <;> positivity
  have one:dist (maximalPaid R r v i j) (maxpart R (target R) i j)=f j:=by
    by_cases tag:F.grades j=(levels i,levels i/2)
    · change dist (if F.grades j=(levels i,levels i/2) then ((r:ℂ)^(levels i))⁻¹*v i j else 0)
          (if F.grades j=(levels i,levels i/2) then u j else 0)=_
      simp only [tag,if_true,f,dist_eq_norm,Complex.ofReal_inv,Complex.ofReal_pow]
    · change dist (if F.grades j=(levels i,levels i/2) then ((r:ℂ)^(levels i))⁻¹*v i j else 0)
          (if F.grades j=(levels i,levels i/2) then u j else 0)=_
      simp only [tag,if_false,f,dist_self]
  have small:f j≤error F ((r^(levels i))⁻¹) (v i) u:=Finset.single_le_sum (f:=f) (fun j _=>good j) (mem_univ j)
  have positive (s:Fin 3):0≤error ((C₀).labels.level (levels s)) ((r^(levels s))⁻¹) (v s)
      (ladder C₀ (index A (grade s)) (source C₀ univ s)):=by
    unfold error
    exact Finset.sum_nonneg fun _ _=>by split <;> positivity
  rw [one]
  exact small.trans (Finset.single_le_sum (fun s _=>positive s) (mem_univ i))

variable {f:Extraction.Order} {Y:Ultrafilter (ℕ×ℕ)} {H:(Bel R.family.book).Hierarchy} {T:Table R.family.book}
local notation "cut"=>trail.curry (Y:Filter (ℕ×ℕ))

/-- The exact upper solve on the whole public roster supplies its required signed field limit. -/
theorem original (simple:G.Simple)(shop:WilsonReportingAbsoluteInletSimultaneous.StationInvoice R)
    (F:Final C₀ f T)(J:ℝ→tower T)(V:Store G)(A:ℝ→Group C₀ 6)
    (book:Book (f:=f) (l:=Y) (H:=H) A J)(lead:Leading F J)(q:ℕ)(prior:(Y:Filter _)≤f.fuse)
    (v:ℝ×(ℕ×ℕ)→∀i,Axes R i)
    (paid:∀ᶠ w in cut,∀i,Solved R (WilsonPositionCorrectedCap.adjusted F J V A w.1) q w.2.1 w.2.2 univ i (v w i)):
    ∀i,Tendsto (fun w=>maximalPaid R w.1 (v w) i) cut (𝓝 (maxpart R (target R) i)):=by
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  apply Metric.tendsto_nhds.mpr
  intro δ δpos
  apply eventually_curry_iff.mpr
  filter_upwards [WilsonOriginalNullReleasedMaximalLimit.original R simple shop F J V A book lead q δpos,
    eventually_curry_iff.mp paid] with r candidates stock
  filter_upwards [candidates.filter_mono prior,stock] with z tested given
  let A₀:=WilsonPositionCorrectedCap.adjusted F J V A r
  exact (entry R A₀ r (v (r,z)) i j).trans_lt (tested univ (v (r,z)) (fun s _=>given s))

end YM.Integration.WilsonOriginalNullReleasedGalopFit
end
