import YM.Integration.WilsonReportCashier
import YM.RG17.Ledger

/-! The actual regulated Wilson vacuum measurement through the original
ordered cutoff filter. No convergence of an approximate coarse expression
is assumed. The coupling is the positive extracted value at the same stop. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportCashierLimit
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction
open Next.Rank Next.Rank.Spindle OPE OPE.Yarn OPE.Strobe OPE.Strobe.Vista26
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Daisy.Charity.RG12
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open Table OPE.Orbits RG12 RG17 WilsonReportFineSmear PertExtension SharpGram.Allow
open scoped Topology BigOperators Classical
universe u
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} {F : Spec.Final C f S}

/-- The actual admitted continuum test, with its independently fixed layout
and the very same original vacuum insertion as the finite Wilson packet. -/
def read (L : Layout F) (T : Test 1) {n : ℕ} (d : Fin (n+1)→ℕ)
    (v : (j:Fin (n+1))→C.label (d j)) (r : ℝ) (ψ : Test (n+1)) : ℂ :=
  let X := RG17.cashier F T
  (RG17.shape X r ψ).applyTo fun y => S.useAt S y (Fin.append (tags (S:=S) (d:=d)
    (fun j => RG17.master L (d j) r (v j))) X.tags)

/-- Every regulator approximation is compared to the fixed continuum
measure after taking its original filter. The exact finite offset remains
inside the coarse expression. A separate early or MS limit is not assumed. -/
theorem on_run {R : Run G} (hG : G.Simple) {U : Campaign R} (W : Campaign.Pillars R U)
    {δ : ℝ} (original : FundedOriginalProperties.{u} hG δ W)
    (subsidy : WilsonReportColumnSubsidy.Eligible R.kit) (pace : WilsonWindowReportingPace.Slow R.kit)
    {S : Table R.family.book} {f : Extraction.Order} {F : Spec.Final R.family f S}
    (L : Layout F) (Z : Ledger L) (T : Test 1) {n : ℕ} (d : Fin (n+1)→ℕ) (t q : ℕ) {ε : ℝ} (hε : 0<ε)
    {K : Set (Points (n+1))} (hK : IsCompact K) (hc : K⊆conf _) (B : ℕ) (big : 17≤B) :
    ∀ᶠ r in RG17.home,let C := R.family
    let k := WilsonMeasuredWindow.stop C.path.levels hG B r
    let g := (Real.sqrt (Z.B k))⁻¹
    ∀ v : (j:Fin (n+1))→C.label (d j),∀ ψ : Test (n+1),tsupport ψ⊆K →
    ∀ b : ℝ,Demand 0 ψ b → ∀ᶠ i : UVIndex in L.lens,∃ (hk : k < i.1),
    let V := fun j => RG17.atRef L (d j) r i (v j)
    (∀ j,Spindle.paid C (d j) k i.1 i.2 (V j)≤C.path.levels.clock.hatBeta k^t) →
    let X := RG17.cashier F T
    let op := RG17.shape X r ψ
    let E := RG17.refTags X
    ‖read L T d v r ψ-∑ y : Sites C i.1 i.2 (n+1) X.n,weight C op y*
        (sampled hk.le d V E y+offset hk.le d V E y)‖ ≤ ε*b*g^q := by
  let C := R.family
  let stop := WilsonMeasuredWindow.stop C.path.levels hG B
  have shapes := WilsonReportCashier.on_run hG W original subsidy pace L T d t q (by positivity : 0<ε/4) hK hc B big
  have parents := eventually_all.mpr fun j : Fin (n+1) => Z.reach.growing.eventually_ge_atTop (C.ref (d j))
  letI := L.notbot
  filter_upwards [shapes,parents] with r stamped refs
  let k := stop r
  let g := (Real.sqrt (Z.B k))⁻¹
  have gb : 0<Z.B k := beta_pos (Running.band f C R.makes hG Z.asymptotic k)
  have gp : 0<g := inv_pos.mpr (Real.sqrt_pos.mpr gb)
  have act : Tendsto (fun i : UVIndex => Pert.Asymptotics.regulatorRun C i.1 i.2 k) L.lens (𝓝 g) :=
    (((Z.asymptotic k).sqrt).inv₀ (Real.sqrt_pos.mpr gb).ne').mono_left L.certified
  have lift : ∀ᶠ i : UVIndex in L.lens, k < i.1 ∧ ∀ (v : (j:Fin (n+1))→C.label (d j))
      (ψ : Test (n+1)) (b : ℝ),∀ hk : k < i.1,
      (∀ j,Spindle.paid C (d j) k i.1 i.2 (RG17.atRef L (d j) r i (v j))≤C.path.levels.clock.hatBeta k^t) →
      tsupport ψ⊆K → Demand 0 ψ b →
      let X := RG17.cashier F T
      let op := RG17.shape X r ψ
      let E := RG17.refTags X
      let V := fun j => RG17.atRef L (d j) r i (v j)
      ‖RG17.packMark L X d v r ψ i-∑ y : Sites C i.1 i.2 (n+1) X.n,weight C op y*
          (sampled hk.le d V E y+offset hk.le d V E y)‖ ≤ (ε/4)*b*Pert.Asymptotics.regulatorRun C i.1 i.2 k^q := by
    apply Filter.Eventually.filter_mono L.certified
    change ∀ᶠ nP : ℕ in atTop,∀ᶠ nN : ℕ in atTop, _
    filter_upwards [f.per.cofinal.eventually stamped] with nP honest
    filter_upwards [f.mesh.cofinal.eventually_gt_atTop k] with nN ht
    refine ⟨ht,?_⟩
    intro v ψ b step funds supp demand
    exact (honest _ step v funds ψ supp b demand).2
  dsimp only
  intro v ψ inside b paid
  let X := RG17.cashier F T
  let op := RG17.shape X r ψ
  let target := read L T d v r ψ
  have goal : Tendsto (RG17.packMark L X d v r ψ) L.lens (𝓝 target) := RG17.limitPack L X le_rfl v ψ refs
  by_cases hb : b=0
  · have bare (x) : ψ x=0 := by
      have pt : ‖ψ x‖≤b := by simpa only [norm_iteratedFDeriv_zero] using paid.smooth 0 le_rfl x
      exact norm_le_zero_iff.mp (pt.trans_eq hb)
    have zero (z) : op z=0 := by
      by_cases ok : r≠0 ∧ RG17.packs X r ψ
      · change RG17.shape X r ψ z=0
        rw [RG17.shaped X ok.1 ok.2]
        simp [RG17.absolute,bare]
      · unfold op RG17.shape; rw [dif_neg ok]; rfl
    filter_upwards [lift] with i hi
    refine ⟨hi.1,?_⟩
    intro _
    have out : read L T d v r ψ=0 := by
      change (∫ z,op z*_)=0
      simp only [zero,zero_mul,integral_zero]
    rw [out,hb,mul_zero,zero_mul]
    change ‖0-∑ y : Sites C i.1 i.2 (n+1) X.n,weight C op y*_‖ ≤ 0
    simp [WilsonReportFineSmear.weight,zero]
  have hbpos := lt_of_le_of_ne paid.nonneg (Ne.symm hb)
  have rate := pow_pos gp q
  have tol : 0<ε*b*g^q/2 := by positivity
  have fitted := (Metric.tendsto_nhds.mp goal) _ tol
  have weak := (act.pow q).eventually (eventually_lt_nhds (show g^q<2*g^q by linarith only [rate]))
  filter_upwards [lift,fitted,weak] with i hi close cap
  refine ⟨hi.1,?_⟩
  intro funds
  let V := fun j => RG17.atRef L (d j) r i (v j)
  let coarse := ∑ y : Sites C i.1 i.2 (n+1) X.n,weight C op y*(sampled hi.1.le d V (RG17.refTags X) y+
    offset hi.1.le d V (RG17.refTags X) y)
  have finite : ‖RG17.packMark L X d v r ψ i-coarse‖≤(ε/4)*b*Pert.Asymptotics.regulatorRun C i.1 i.2 k^q :=
    hi.2 v ψ b hi.1 funds inside paid
  have dist : dist target (RG17.packMark L X d v r ψ i) ≤ ε*b*g^q/2 := (dist_comm ..).le.trans close.le
  change ‖target-coarse‖≤ε*b*g^q
  calc
    _ ≤ ‖target-RG17.packMark L X d v r ψ i‖+‖RG17.packMark L X d v r ψ i-coarse‖ := norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ ε*b*g^q/2+((ε/4)*b)*(2*g^q) := add_le_add (by simpa only [dist_eq_norm] using dist)
      (finite.trans (mul_le_mul_of_nonneg_left cap.le (mul_nonneg (by positivity) paid.nonneg)))
    _ = _ := by ring

end YM.Integration.WilsonReportCashierLimit
end

