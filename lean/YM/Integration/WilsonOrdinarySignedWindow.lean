import YM.Integration.WilsonOrdinaryWindowBuyer

/-! One actual signed local insertion and one common reflected insertion on the original
positive coarse Wilson measure. Each already paid registered four-table statistic has
this literal integral presentation before any limit or numerical Taylor comparison. -/

noncomputable section
namespace YM.Integration.WilsonOrdinarySignedWindow
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table Spec
open Next.Rank Next.UVStress OPE OPE.Orbits OPE.Strobe RG12 RG17 RG17.Panoramic SharpGram Climb PhysMS
open OPE.Levy Push.FiniteDetection.Free Trace.Pilot
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonReportRegularMoments WilsonReportReflectedGram WilsonReportEarlySmearing WilsonReportColumnCut
open WilsonOrdinaryHomogeneousDetectors WilsonOrdinaryWindowBuyer WilsonOrdinaryFourGram
open WilsonOrdinaryMixedGram WilsonOrdinaryNormalizedStep
open Cells Push.GridApprox
open scoped Topology Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
variable {F : Final R.family f S} {J : ℝ→tower S} {L : Layout F} {g : ℝ→ℝ} {d : ℕ}
variable {A B : Module.End ℂ ((Bel R.family.book).Field d)} {e : ℕ} {r : ℝ}
variable (P : WindowRows F J L g d A B e r)
set_option quotPrecheck false
local notation "k!" => berth R 28 (L.level r)
local notation "b!" => WilsonOrdinaryHomogeneousDetectors.basis F d
local notation "t!" => (Real.exp (1:ℝ))⁻¹

def weight (u : ℝ) : Fin 4 → ℝ := ![1,-1,-u,-(u^2)]
def slot (N p : ℕ) (h : Fin 4) (i : Handle F d) :=
  localized L r d k! N p (P.left h i) (cells R k! p r detectors 0)
def reflected (N p : ℕ) (j : Handle F d) :=
  localized L r d k! N p (P.right j) (cells R k! p r detectors 1)
def net (N p : ℕ) (i : Handle F d) (U : Config G (R.family.side k! p)) : ℂ :=
  ∑ h : Fin 4, (weight (g r) h:ℂ)*slot P N p h i U

/-- The common window of the signed jet is an original bounded, Borel, invariant
local insertion. Its source does not become nonlocal under the finite subtraction. -/
theorem interior (N p : ℕ) (deep : k! < N) (i : Handle F d) :
    Interior (window (cells R k! p r detectors 0) (omen R.family d k! (R.family.path.levels.budget k!).B))
      (net P N p i) := by
  let loc := window (cells R k! p r detectors 0) (omen R.family d k! (R.family.path.levels.budget k!).B)
  have each (h : Fin 4) : Interior loc (fun U => (weight (g r) h:ℂ)*slot P N p h i U) :=
    Interior.scale _ ((P.interior N p deep).1 h i)
  have subtotal (m : Finset (Fin 4)) : Interior loc (fun U => ∑ h ∈ m, (weight (g r) h:ℂ)*slot P N p h i U) := by
    induction m using Finset.induction with
    | empty => simpa using (Interior.constant (G:=G) loc 0)
    | @insert h m hn ih => simpa only [sum_insert hn] using (each h).plus ih
  exact subtotal univ

theorem integral (N p : ℕ) (deep : k! < N) (i j : Handle F d) :
    cut F J L g d P (N,p) i j =
      (∫ U, net P N p i U*reflected P N p j U ∂(OPE.Therm.scene R.family.path N p k!)).re := by
  let μ := OPE.Therm.scene R.family.path N p k!
  letI : IsProbabilityMeasure μ := Therm.probability R.makes.wilson deep.le
  let f := fun h => slot P N p h i
  let v := reflected P N p j
  let w := weight (g r)
  have iv := (P.interior N p deep).2 j
  have vv : RG.Envelope v := ⟨iv.borel,iv.cost⟩
  have integ (h : Fin 4) : Integrable (fun U => f h U * v U) μ := by
    have ih := (P.interior N p deep).1 h i
    have uu : RG.Envelope (f h) := ⟨ih.borel,ih.cost⟩
    exact (uu.mulC vv).integrableC μ
  have spread : (∫ U,net P N p i U*v U ∂μ) =
      ∑ h : Fin 4,(w h:ℂ)*(∫ U,f h U*v U ∂μ) := by
    change (∫ U,(∑ h : Fin 4,(w h:ℂ)*f h U)*v U ∂μ) = _
    simp_rw [sum_mul,mul_assoc]
    rw [integral_finsetSum _ (fun h _ => (integ h).const_mul (w h:ℂ))]
    simp only [integral_const_mul]
  have atSlot (h : Fin 4) : WilsonReportWindowMatrix.joint L d ![P.left h i,P.right j] r k! N p =
      ∫ U,f h U*v U ∂μ := by
    unfold WilsonReportWindowMatrix.joint
    simp only [Fin.prod_univ_two]; rfl
  change signed (g r) (fun h => (WilsonReportWindowMatrix.joint L d ![P.left h i,P.right j] r k! N p).re) =
      (∫ U,net P N p i U*v U ∂μ).re
  simp_rw [atSlot]; rw [spread]
  simp [signed,Fin.sum_univ_succ,w,weight,Complex.mul_re,Complex.mul_im,pow_two]
  ring

/-- Exact normalized, two-source physical buyer at one true cutoff and period. -/
theorem compared (hg : 0 ≤ g r) (cap : g r ≤ 1) : ∀ᶠ z : UVIndex in L.lens, ∀ i j : Handle F d,
    |(mixed F J d r (t!*r) (b! i) (b! j) -
      trialStep F J d r t! (WilsonOrdinaryNormalizedStep.second d (g r) A B) (b! i) (b! j)) -
    (∫ U,net P z.1 z.2 i U * reflected P z.1 z.2 j U ∂(OPE.Therm.scene R.family.path z.1 z.2 k!)).re| ≤ 4*(g r)^2 := by
  filter_upwards [P.read,WilsonOrdinaryWindowBuyer.compared F J L g d P hg cap] with z hz price
  intro i j
  simpa only [integral P z.1 z.2 hz.1 i j] using price i j

end YM.Integration.WilsonOrdinarySignedWindow
