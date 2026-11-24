import YM.Integration.WilsonMatrixOriginalFundedPanel

/-! A single orientation of the original signed row gives a positive measured value. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonMatrixOriginalOrientedPanel
open Filter Function Set MeasureTheory Lattice Wilson RG RG17 Source Marker Extraction Extraction.Order
open Table Spec Climb Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS OPE OPE.Therm
open Next.UVStress Next.Rank.Price PhysicalNext.Repeat.Legato SharpGram.Lenses FVA2 FVA2.Register
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMatrixTicketLanesSmearedRows
open WilsonInvariantActionPairProbe WilsonInvariantActionSpectatorPrices WilsonInvariantActionPairCovariance
open WilsonLimitConstruction WilsonMatrixOriginalSignedPanel WilsonInvariantActionCalibratedColumn
open WilsonMatrixOriginalSignedReading WilsonMatrixOriginalRealFields
open Trace.Sundial WilsonMatrixOriginalFiledPanel Next.Rank OPE.Orbits RG12 SharpGram
open scoped Classical Topology BigOperators

open private response from YM.Integration.WilsonInvariantActionCalibratedColumn

variable {G : Gauge} {R : Run G}

/-- Orient a nonzero limit before its two limiting processes. -/
theorem signed {T : Type*} {U : Filter T} {c : ℝ} (nz : 0 < |c|)
    {x : ℝ → ℝ} {p : ∀ r : ℝ, 0 < r → T → ℝ} (limit : Tendsto x trail (𝓝 c))
    (readout : ∀ᶠ r in trail, ∀ hr : 0 < r, Tendsto (p r hr) U (𝓝 (x r))) :
    ∃ s : ℝ, (s=1 ∨ s= -1) ∧ s*c=|c| ∧ ∀ᶠ r in trail, ∀ hr : 0 < r,
      |c|/2 < s*x r ∧ Tendsto (fun t => s*p r hr t) U (𝓝 (s*x r)) ∧
      ∀ᶠ t in U, |c|/4 < s*p r hr t := by
  obtain ⟨s,unit,orientation⟩ : ∃ s : ℝ, (s=1 ∨ s= -1) ∧ s*c=|c| := by
    by_cases h : 0 ≤ c
    · exact ⟨1,Or.inl rfl,by simp [abs_of_nonneg h]⟩
    · exact ⟨-1,Or.inr rfl,by simp [abs_of_neg (lt_of_not_ge h)]⟩
  have head : Tendsto (fun r => s*x r) trail (𝓝 |c|) := by
    rw [←orientation]
    exact tendsto_const_nhds.mul limit
  refine ⟨s,unit,orientation,?_⟩
  filter_upwards [head.eventually (Ioi_mem_nhds (half_lt_self nz)),readout] with r half at_r
  intro hr
  have fine : Tendsto (fun t => s*p r hr t) U (𝓝 (s*x r)) := tendsto_const_nhds.mul (at_r hr)
  have quarter : |c|/4 < s*x r := by
    change |c|/2 < s*x r at half
    linarith
  exact ⟨half,fine,fine.eventually (Ioi_mem_nhds quarter)⟩

def Signed {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
    (J : ℝ → tower S) (L : Layout F) {U : Filter UVIndex}
    (a b : ℝ → R.family.label 4) (v : ℝ → S.Field 4) (φ : Test 2) (c : ℂ)
    (χ : ℂ →L[ℝ] ℝ) : Prop :=
  0 < |χ c| ∧ ∃ s : ℝ, (s=1 ∨ s= -1) ∧ s*χ c=|χ c| ∧ ∀ᶠ r in trail, ∀ hr : 0 < r,
    let z := χ (tested (J r 4 (stepField R.family)) (v r) r φ)
    |χ c|/2 < s*z ∧ Tendsto (fun t => s*Value F L a b χ φ hr t) U (𝓝 (s*z)) ∧
    ∀ᶠ t in U, |χ c|/4 < s*Value F L a b χ φ hr t

def Observation {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
    (J : ℝ → tower S) (Z : WilsonPrescription G) (H : (Bel R.family.book).Hierarchy)
    (L : Layout F) : Prop :=
    ∃ (D:Profiles R 4) (j:D.probes.index) (v₀:(standard R.family.labels).Ref 4)
      (hs:D.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 v₀)
      (e:ℕ) (deposit:ℝ→RG17.Free R.family 4→R.family.label 4) (χ:ℂ→L[ℝ]ℝ),
      let φ := WilsonInvariantActionCalibratedColumn.packet v₀ hs (test D j)
      let v := (Bel R.family.book).project 4 v₀
      let b := fun r => homogeneous F J Z r 4 v
      let c := tree (D.probes.shell j) (test D j) H 4 (stepField R.family)
      (χ=Complex.reCLM ∨ χ=Complex.imCLM) ∧
      Signed (U:=L.lens) F J L (fun r => deposit r (stepField R.family)) (fun r => deposit r (freeInput F J Z 4 r v)) b φ c χ ∧
      (∀ᶠ r in trail,∀u:RG17.Free R.family 4,master L 4 r (deposit r u)=J r 4 u ∧
        ∀N n,L.level r ≤ N→quota R.family 4 (L.level r) N n (atRef L 4 r (N,n) (deposit r u)) ≤
          R.family.S.a (L.level r)^4*(R.family.path.levels.clock.hatBeta (L.level r)^e*‖u‖))


theorem observed {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
    (J : ℝ → tower S) (Z : WilsonPrescription G) {H : (Bel R.family.book).Hierarchy}
    (lead : Leading F J) (paid : ∀ d : ℕ, ∀ᶠ r in trail, Frame.obedient F H (J r) d)
    (simple : G.Simple) (central : ∀ᶠ r in trail, AlignV F.room.kernel F.sector H (J r 4))
    (L : Layout F) (seen : WilsonMatrixOriginalFundedPanel.Observation F J Z H L) : Observation F J Z H L := by
  obtain ⟨D,j,w,sites,e,deposit,χ,which,filed,quota⟩ := seen
  let φ := packet w sites (test D j)
  let v := (Bel R.family.book).project 4 w
  let b := fun r => homogeneous F J Z r 4 v
  let c := tree (D.probes.shell j) (test D j) H 4 (stepField R.family)
  let cov := fun r => tested (J r 4 (stepField R.family)) (b r) r φ
  have converge : Tendsto cov trail (𝓝 c) := by
    change Tendsto _ _ (𝓝 (tree (D.probes.shell j) (test D j) H 4 (stepField R.family)))
    rw [response w sites]
    exact WilsonInvariantActionCompensatedPair.original F J Z lead paid simple w central φ
  refine ⟨D,j,w,sites,e,deposit,χ,which,⟨filed.1,?_⟩,quota⟩
  apply signed filed.1 (χ.continuous.continuousAt.tendsto.comp converge)
  filter_upwards [filed.2] with r n
  exact fun hr => (n hr).2.1

theorem on_run (simple : G.Simple) {ρ : ℝ} {T : Campaign R} (W : Campaign.Pillars R T)
    (funded : FundedOriginalProperties.{u} simple ρ W) (pace : WilsonWindowReportingPace.Slow R.kit)
    (Z : WilsonPrescription G) {B : ℕ} (hB : 0 < B) (v : Extraction.Order) :
    ∃ (w : Extraction.Order) (S : Table R.family.book) (F : Final R.family (v.refine w) S)
      (H : (Bel R.family.book).Hierarchy) (J : ℝ → tower S) (L : Layout F),
      Leading F J ∧ (∀ d : ℕ, ∀ᶠ r in trail, Frame.obedient F H (J r) d) ∧
      L.level = WilsonMeasuredWindow.stop R.family.path.levels simple B ∧ L.lens ≤ (v.refine w).fuse ∧
      Observation F J Z H L := by
  obtain ⟨w,S,F,H,arch,l,J,A,δ,u₀,bank,L,bliss,lead,obey,same,align,cal,coupling,pegs,level,lens,seen⟩ :=
    WilsonMatrixOriginalFundedPanel.on_run simple W funded pace Z hB v
  have centered : ∀ᶠ r in trail, AlignV F.room.kernel F.sector H (J r 4) :=
    (same.and align).mono fun _ h => h.1.symm ▸ h.2
  exact ⟨w,S,F,H,J,L,lead,obey,level,lens,observed F J Z lead obey simple centered L seen⟩

end YM.Integration.WilsonMatrixOriginalOrientedPanel
end
