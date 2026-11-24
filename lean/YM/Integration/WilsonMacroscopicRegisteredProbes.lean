import YM.Integration.WilsonMacroscopicFirstOmitted
import YM.Integration.WilsonPhysicalExteriorDetector

/-! Bind the actual physical grade reader to the registered numerical far
bank. Its ideal readings are literally the held macroscopic correlations
on the original state; the same exact calibration exists at finite cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicRegisteredProbes
open Function Filter Finset Set MeasureTheory Extraction Table Spec
open Next.Rank OPE OPE.Orbits OPE.Nesting RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonExteriorPortfolio
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {V : Table R.family.book}
local notation "FreeState" => Bel R.family.book

/-- The labels and offsets of the registered far row. The zero test is
unused: this is a point observation at the bank's actual registered site. -/
def external (J : ℝ→PhysMS.tower V) (τ : ℝ) (e : ExteriorData FreeState) : RG17.External R.family V where
  n := e.length
  tags := WilsonExteriorPortfolio.carried J τ ∘ OPE.tags FreeState e
  test := 0

def site (τ : ℝ) (e : ExteriorData FreeState) := τ • WilsonExteriorPortfolio.points FreeState e

private theorem outerRoom (X : RG17.External R.family V) (z : Points (X.n+1)) (good : z∈conf (X.n+1)) : ∃ δ : ℝ,0<δ ∧ ClearOf 0 (X.offset z) δ := by
  have compact : IsCompact ({z} : Set (Points (X.n+1))) := isCompact_singleton
  obtain ⟨T,η,hT,hη,hx⟩ := RG17.roomCosts compact (Set.singleton_subset_iff.mpr good)
  refine ⟨η,hη,?_⟩
  have fits := hx 1 one_pos z (mem_singleton z)
  constructor
  · intro j;have h := fits.spaced 0 j.succ (Ne.symm (Fin.succ_ne_zero j))
    simpa [posed,RG17.External.offset] using h
  · intro j k ne
    simpa [RG17.External.offset,posed] using (fits.spaced j.succ k.succ (Fin.succ_injective _ |>.ne ne))

theorem room (J : ℝ→PhysMS.tower V) {τ : ℝ} (ht : 0<τ) (e : ExteriorData FreeState) (he : Apt e) :
    ∃ δ : ℝ,0<δ ∧ ClearOf 0 ((external J τ e).offset (site (R:=R) τ e)) δ :=
  outerRoom (external J τ e) (site (R:=R) τ e) (Work.A05.smul_conf ht ((generic_conf _) he))

/-- Exact equality with the specific bank's original signed linear reading,
on a physical (not formal) field in V.Field h. -/
theorem numerical (F : Spec.Final R.family f V) (J : ℝ→PhysMS.tower V) {h : ℕ} (U : Detector FreeState h) {τ : ℝ} (ht : 0<τ) (i : Fin U.size) (v : V.Field h) :
    let e := U.listen i
    let X := external J τ e
    (bank J U V τ ((J τ h).symm v)) i = upon V h 0 (X.offset (site (R:=R) τ e)) X.labels v := by
  let e := U.listen i
  let X := external J τ e
  let z := site (R:=R) τ e
  let u := (J τ h).symm v
  have atSite : z∈conf (e.length+1) := Work.A05.smul_conf ht ((generic_conf _) (U.awake i))
  have row := X.pay_eq F h v z atSite
  have tags : Fin.cons (⟨h,v⟩ : V.Tag) X.tags = fun j=>carried J τ (word FreeState e u j) := by
    funext j;refine Fin.cases ?_ (fun l=>?_) j
    · change (⟨h,v⟩ : V.Tag)=⟨h,J τ h u⟩;rw [(J τ h).apply_symm_apply]
    · rfl
  change WilsonExteriorPortfolio.row J V τ h e u = X.pay h v z
  refine (WilsonExteriorPortfolio.row_read J V τ h e u).trans ?_
  exact (row.trans (congrArg (V.useAt V z) tags)).symm

def grade (F : Spec.Final R.family f V) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J : ℝ→PhysMS.tower V) {h : ℕ} (U : Detector FreeState h) (T : Table R.family.book) (τ : ℝ) :
    (Fin U.size→ℂ) →ₗ[ℂ] V.Field h :=
  (Q.cutTest h h).comp ((J τ h).toLinearMap.comp (decoder U.report (bank J U T τ)))

private theorem calibrated (F : Spec.Final R.family f V) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J : ℝ→PhysMS.tower V) {h : ℕ} (U : Detector FreeState h)
    (T : Table R.family.book) (τ : ℝ) (p : priced U.report (bank J U T τ)) (v : V.Field h) : grade F Q J U T τ (bank J U T τ ((J τ h).symm v))=Q.cutTest h h v := by
  change Q.cutTest h h (J τ h (decoder U.report (bank J U T τ) (bank J U T τ ((J τ h).symm v))))=Q.cutTest h h v
  rw [p.1,(J τ h).apply_symm_apply]

/-- Real readout portability. This is also the exact grade projection on
the authentic regulated numerical bank at all of its purchased cutoffs. -/
theorem original (F : Spec.Final R.family f V) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J : ℝ→PhysMS.tower V) (leading : PhysMS.Leading F J)
    (fac : OPE.Facilities R.family f V) {h : ℕ} (U : Detector FreeState h) : ∀ᶠ τ in RG17.home,
      (∀ v : V.Field h,grade F Q J U V τ (bank J U V τ ((J τ h).symm v))=Q.cutTest h h v) ∧
      ∀ᶠ a : ℕ×ℕ in f.fuse,∀ v : V.Field h,
        let T := StressFlux.Matching.rounded R.family a.1 a.2
        grade F Q J U T τ (bank J U T τ ((J τ h).symm v))=Q.cutTest h h v := by
  obtain ⟨continuum,finite⟩ := WilsonExteriorPortfolio.portfolio F J leading fac.toServices U
  filter_upwards [continuum,finite] with τ a b
  exact ⟨calibrated F Q J U V τ a,b.mono fun z hz=>calibrated F Q J U _ τ hz⟩

end YM.Integration.WilsonMacroscopicRegisteredProbes
