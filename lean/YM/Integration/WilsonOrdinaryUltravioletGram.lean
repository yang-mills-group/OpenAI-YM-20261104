import YM.Integration.WilsonOrdinaryUltravioletLimit
import YM.Integration.WilsonReportDetectorMesh
import YM.Integration.WilsonReportSignedLabel

/-! The actual microscopic signed two-mark sum converges without loss to the
physical discrepancy required by the original exterior matrix argument. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryUltravioletGram
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table Spec
open Next.Rank Next.UVStress OPE OPE.Orbits OPE.Strobe RG12 RG17 RG17.Panoramic SharpGram Climb PhysMS
open OPE.Levy Push.FiniteDetection.Free Trace.Pilot
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonReportRegularMoments WilsonReportReflectedGram WilsonReportEarlySmearing WilsonReportColumnCut
open WilsonOrdinaryMixedGram WilsonOrdinaryNormalizedStep WilsonOrdinaryFourGram
open WilsonOrdinaryHomogeneousDetectors WilsonOrdinaryMeasuredMarch
open Cells Push.GridApprox
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}

open WilsonOrdinaryWindowBuyer WilsonReportSignedLabel WilsonOrdinarySignedWindow
open WilsonOrdinaryUltravioletPair
variable {F : Final R.family f S} (J : ℝ→tower S) (L : Layout F) (g : ℝ→ℝ) (d : ℕ)
local notation "t!" => (Real.exp (1:ℝ))⁻¹
local notation "b!" => WilsonOrdinaryHomogeneousDetectors.basis F d

/-- The original normalized two-mark cutoff value on the genuine fine sites.
The two restored vectors depend on *both* regulator parameters. -/
def deposited {r : ℝ} {A B : Module.End ℂ ((Bel R.family.book).Field d)} {e : ℕ} (P : WindowRows F J L g d A B e r)
    (i j : Handle F d) (u : UVIndex→ℝ) (z : UVIndex) : ℝ :=
  let x := wrap (R.family.side z.1 z.2) ∘ address (R.family.S.a z.1) (r • detectors)
  let a := RG17.atRef L d r z (WilsonReportSignedLabel.input P i)
  let b := RG17.atRef L d r z (P.right j)
  (∑ q,∑ t,(coefficient R d z.1 z.2 a (u z) q * coefficient R d z.1 z.2 b (u z) t) *
    Wilson.moment (R.family.beta z.1 z.2) (fun U=>
      enrolled R d z.1 z.2 (u z) q (x 0) U*enrolled R d z.1 z.2 (u z) t (x 1) U)).re

private theorem view (present : Pier.Lair.Present F J) :
    ∀ᶠ r in RG17.home,∀ (s:ℝ) (v w : RG17.Free R.family d),
      (linear₂ (S.classMoment S (fun _:Fin 2=>d) (r • detectors)) (J s d v) (J r d (adjoint R d w))).re =
      mixed F J d r s v w := by
  filter_upwards [WilsonReportDetectorMesh.reflected F J present d] with r result
  intro s v w
  let a := (J r d).symm (J s d v)
  let b := adjoint R d w
  have same : (fun k=>J r d ((![a,b] : Fin 2→_) k)) = ![J s d v,J r d b] := by
    funext k
    fin_cases k
    · exact (J r d).apply_symm_apply _
    · rfl
  have heard := result s v w
  change _=(S.classMoment S (fun _ : Fin 2=>d) (r • detectors) (fun k=>J r d ((![a,b] : Fin 2→_) k))).re at heard
  rw [same] at heard
  exact heard.symm

private theorem real_sum {E : Type*} [AddCommGroup E] [Module ℂ E] (M : E →ₗ[ℂ] E →ₗ[ℂ] ℂ)
    (v : Fin 4→E) (w : E) (a : ℝ) :
    (M (∑h,(weight a h:ℂ) • v h) w).re = signed a (fun h=>(M (v h) w).re) := by
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]
  simp [signed,WilsonOrdinarySignedWindow.weight,Fin.sum_univ_succ,pow_two,Complex.mul_re,Complex.mul_im]
  ring

private theorem physical {r : ℝ} {A B : Module.End ℂ ((Bel R.family.book).Field d)} {e : ℕ}
    (P : WindowRows F J L g d A B e r) (i j : Handle F d)
    (read : ∀ (s:ℝ) (v w : RG17.Free R.family d),
      (linear₂ (S.classMoment S (fun _:Fin 2=>d) (r • detectors)) (J s d v) (J r d (adjoint R d w))).re =
      mixed F J d r s v w) :
    (S.classMoment S (fun _ : Fin 2=>d) (r • detectors) (fun k=>master L d r
      ((![WilsonReportSignedLabel.input P i,P.right j] : Fin 2→_) k))).re =
      mixed F J d r (t!*r) (b! i) (b! j) - trialStep F J d r t! (second d (g r) A B) (b! i) (b! j) := by
  let M := linear₂ (S.classMoment S (fun _ : Fin 2=>d) (r • detectors))
  let v h := J (radii r t! h) d (columns d t! A B (b! i) h)
  let w := J r d (adjoint R d (b! j))
  have slots : (fun k=>master L d r ((![WilsonReportSignedLabel.input P i,P.right j] : Fin 2→_) k)) =
      ![master L d r (WilsonReportSignedLabel.input P i),w] := by
    funext k
    fin_cases k
    · rfl
    · exact P.second j
  rw [slots,WilsonOrdinaryFourGram.split F J d r t! (g r) A B (b! i) (b! j)]
  change (M (master L d r (WilsonReportSignedLabel.input P i)) w).re = _
  rw [WilsonReportSignedLabel.registered_master P i]
  change (M (∑h,(weight (g r) h:ℂ) • v h) w).re = _
  rw [real_sum]
  apply congrArg (signed (g r))
  funext h
  exact read _ _ _

/-- With all labels on the already selected original layout, the fixed
physical ratio is the limit of the same single signed two-mark input. -/
theorem original (hG : G.Simple) (present : Pier.Lair.Present F J)
    {filt : Filter UVIndex} {Q : Lenses.Mantle F filt} (pegs : Pegs Q L) :
    ∀ᶠ r in RG17.home,∀ (A B : Module.End ℂ ((Bel R.family.book).Field d)) (e : ℕ) (P : WindowRows F J L g d A B e r)
      (i j : Handle F d) (u : UVIndex→ℝ), (∀ z,u z≠0) →
      Tendsto (deposited J L g d P i j u) L.lens
        (𝓝 (mixed F J d r (t!*r) (b! i) (b! j) -
          trialStep F J d r t! (second d (g r) A B) (b! i) (b! j))) := by
  have positive : ∀ᶠ r in RG17.home,0<r := self_mem_nhdsWithin
  filter_upwards [positive,pegs.level.growing.eventually_ge_atTop (R.family.ref d),
    view J d present] with r hr grade reflected
  intro A B e P i j u available
  have raw := WilsonOrdinaryUltravioletLimit.two L hG r d (WilsonReportSignedLabel.input P i)
    (P.right j) grade (r • detectors) (Work.A05.smul_conf hr detectors_in) u available
  have actual := Complex.continuous_re.continuousAt.tendsto.comp raw
  rw [←physical J L g d P i j reflected]
  exact actual

/-- A cutoff estimate on the genuine combined UV source is already a real
numerical estimate at the physical radius. The passage to the original
continuum costs no constant and no power. -/
theorem price {r : ℝ} {A B : Module.End ℂ ((Bel R.family.book).Field d)} {e : ℕ} (P : WindowRows F J L g d A B e r)
    (i j : Handle F d) (u : UVIndex→ℝ) (c : ℝ)
    (realized : Tendsto (deposited J L g d P i j u) L.lens
      (𝓝 (mixed F J d r (t!*r) (b! i) (b! j) - trialStep F J d r t! (second d (g r) A B) (b! i) (b! j))))
    (paid : ∀ᶠ z in L.lens,|deposited J L g d P i j u z|≤c*(g r)^2) :
    |mixed F J d r (t!*r) (b! i) (b! j) - trialStep F J d r t! (second d (g r) A B) (b! i) (b! j)|≤c*(g r)^2 := by
  letI := L.notbot
  exact le_of_tendsto (continuous_abs.continuousAt.tendsto.comp realized) paid

end YM.Integration.WilsonOrdinaryUltravioletGram
