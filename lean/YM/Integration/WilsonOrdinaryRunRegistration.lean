import YM.Integration.WilsonOrdinaryComplexPivot
import YM.RG12.Canonical.Refinement

/-! Exact recovery of a microscopic source at the original reporting
level. Bounded *corrected* reporting coordinates on the preselected
ultrafilter represent one actual continuum field against all separated
profiles; no equality to a perturbative table is built into the source. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryRunRegistration
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table Spec
open Next.Rank Next.UVStress OPE OPE.Orbits OPE.Strobe RG12 RG17 RG17.Panoramic SharpGram Climb PhysMS
open OPE.Levy Push.FiniteDetection.Free Trace.Pilot
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonReportRegularMoments WilsonReportReflectedGram WilsonReportEarlySmearing WilsonReportColumnCut
open WilsonOrdinaryMixedGram WilsonOrdinaryNormalizedStep WilsonOrdinaryFourGram
open WilsonOrdinaryHomogeneousDetectors WilsonOrdinaryMeasuredMarch
open Cells Push.GridApprox FullVolume
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}

open WilsonOrdinaryHomogeneousDetectors

open MS MS.Menus MS.Local.Physical FVAAlt2 FVA2 Extra.Histories
open RegulatorIR.FVAAlt2.Lodge WilsonFactoryFiledGlyphs WilsonOrdinaryUltravioletPair
open WilsonOrdinaryPositionDecoder WilsonOrdinaryHomogeneousDetectors
variable {F : Final R.family f S} (L : Layout F) (d : ℕ)
variable {B : Deck G}


/-- Exact inverse to the native reporting-to-cutoff map, including the
dimension charge and original (possibly nonidentity) shift. -/
def report (r : ℝ) (z : UVIndex) : R.family.label d→ₗ[ℂ]R.family.label d :=
  ((R.family.S.a (L.level r)^d : ℝ):ℂ)⁻¹ •
    (L.shift d r).symm.toLinearMap.comp (RG12.charts R.family F.room.cutoff d (L.level r) z).toLinearMap

theorem unroll (r : ℝ) (z : UVIndex) (a : R.family.label d) :
    RG17.atRef L d r z (report L d r z a)=a := by
  let A : ℂ := (R.family.S.a (L.level r)^d : ℝ)
  have nonzero : A≠0 := Complex.ofReal_ne_zero.mpr (pow_ne_zero d (R.family.S.a_pos (L.level r)).ne')
  let T := RG12.charts R.family F.room.cutoff d (L.level r) z
  change A • T.symm ((L.shift d r) (A⁻¹ • (L.shift d r).symm (T a)))=a
  rw [map_smul,LinearEquiv.apply_symm_apply,map_smul,LinearEquiv.symm_apply_apply,smul_smul,mul_inv_cancel₀ nonzero,one_smul]

/-- Cancellation of the genuine filed terminal BEFORE its price: what remains
is the received actual primary at the reporting date itself. -/
theorem filed (r : ℝ) (z : UVIndex) (v : MS.Rake.Label B) (u : ℝ)
    (admit : R.family.ref v.h ≤ L.level r) (depth : L.level r ≤ z.1) :
    let T := R.family.factory v.h z.1 z.2
    let G := R.family.labels.level v.h
    let θ := R.family.path.levels.clock.threshold z.1
    report L v.h r z (ledger R v z.1 z.2 u)=
      ((R.family.S.a (L.level r)^v.h : ℝ):ℂ)⁻¹ • (L.shift v.h r).symm
        (T.entries (L.level r) (G.scaled (u/θ)⁻¹ (Lobby.γ (basisR R) v))).x := by
  let T := R.family.factory v.h z.1 z.2
  let V := (R.family.labels.level v.h).scaled (u/R.family.path.levels.clock.threshold z.1)⁻¹ (Lobby.γ (basisR R) v)
  have exactChart : RG12.charts R.family F.room.cutoff v.h (L.level r) z (ledger R v z.1 z.2 u)=(T.entries (L.level r) V).x := by
    rw [RG12.charts,dif_pos ⟨admit,depth⟩]
    change (T.entries (L.level r) (T.terminal.symm (T.terminal V))).x=(T.entries (L.level r) V).x
    rw [LinearEquiv.symm_apply_apply]
  let a : ℂ := (R.family.S.a (L.level r)^v.h : ℝ)
  change a⁻¹ • (L.shift v.h r).symm (RG12.charts R.family F.room.cutoff v.h (L.level r) z (ledger R v z.1 z.2 u)) = a⁻¹ • (L.shift v.h r).symm (T.entries (L.level r) V).x
  rw [exactChart]

/-- A real boundedness purchase in the native finite-dimensional reporting
space suffices to identify the original moving microscopic labels on the
already selected physical ultrafilter. -/
theorem compact (r : ℝ) (u : Ultrafilter UVIndex) (prior : (u:Filter UVIndex)≤L.lens)
    (w : UVIndex→R.family.label d) (admit : R.family.ref d ≤ L.level r)
    (A : ℝ) (price : ∀ᶠ z in (u:Filter UVIndex), ‖report L d r z (w z)‖≤A) :
    ∃ v : R.family.label d, Tendsto (fun z=>report L d r z (w z)) (u:Filter UVIndex) (𝓝 v) ∧
      Tendsto w (u:Filter UVIndex) (𝓝 (RG17.locatedRef L d r v)) := by
  obtain ⟨v,hv⟩ := RG12.ultrafilter_converges u (fun z=>report L d r z (w z)) A price
  refine ⟨v,hv,?_⟩
  have step := RG17.tendsRef L prior hv admit
  simpa only [unroll] using step

/-- The very same original field represents all corrected insertions against
every separated compact profile, in every finite arity, with the actual
microscopic functional and all sites prior to the common cutoff tail. -/
theorem exterior (hG : G.Simple) (r : ℝ) (u : Ultrafilter UVIndex)
    (prior : (u:Filter UVIndex)≤L.lens) {n : ℕ} (e : Caps n) (w : UVIndex→R.family.book.Vector e)
    (admit : ∀ j,R.family.ref (e j) ≤ L.level r)
    (price : ∀ j,∃ A : ℝ,∀ᶠ z in (u:Filter UVIndex),‖report L (e j) r z (w z j)‖≤A) :
    ∃ v : R.family.book.Vector e,
      (∀ j,Tendsto (fun z=>report L (e j) r z (w z j)) (u:Filter UVIndex) (𝓝 (v j))) ∧
      ∀ K : Set (Points n),IsCompact K → K ⊆ conf n → ∀ ε : ℝ,0<ε →
        ∀ᶠ z in (u:Filter UVIndex), ∀ x : Positions n,tag (R.family.S.a z.1) x ∈ K →
          dist (R.family.ensemble (N:=z.1) (p:=z.2) e (wrap _ ∘ x) (w z))
            (S.classMoment S e (tag (R.family.S.a z.1) x) (fun j=>master L (e j) r (v j))) < ε := by
  have each (j : Fin n) := compact L (e j) r u prior (fun z=>w z j) (admit j) (price j).choose (price j).choose_spec
  choose v hv hw using each
  refine ⟨v,hv,?_⟩
  intro K hk sep ε he
  let c (j : Fin n) := RG17.locatedRef L (e j) r (v j)
  have bought := WilsonMovingCalibratedFields.paid R hG F (prior.trans L.certified) e w c hw K hk sep ε he
  filter_upwards [bought] with z ready x inside
  have eq : S.value e (tag (R.family.S.a z.1) x) c=S.classMoment S e (tag (R.family.S.a z.1) x) (fun j=>master L (e j) r (v j)) := by
    simp_rw [←RG17.payRef]
    exact (S.at_project S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) (sep inside) (fun j=>⟨e j,c j⟩)).symm
  rw [←eq]
  exact ready x inside

end YM.Integration.WilsonOrdinaryRunRegistration
