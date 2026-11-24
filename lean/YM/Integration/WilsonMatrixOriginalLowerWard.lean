import YM.Integration.WilsonMatrixOriginalEarlierPanel

/-! The original Ward normalization read from the same nonzero signed lower Wilson row. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalLowerWard
open Filter Function Set MeasureTheory Lattice Wilson RG RG17 Source Marker Extraction
open Table Spec Climb Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS OPE OPE.Therm
open Next.UVStress Next.Rank.Price PhysicalNext.Repeat.Legato SharpGram.Lenses FVA2 FVA2.Register
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMatrixTicketLanesSmearedRows
open WilsonInvariantActionPairProbe WilsonInvariantActionSpectatorPrices WilsonInvariantActionPairCovariance
open WilsonInvariantActionCalibratedColumn WilsonInvariantActionPosition WilsonInvariantActionCapturedProfile
open WilsonMatrixOriginalEarlierPanel
open private component from YM.Integration.WilsonMatrixOriginalEarlierPanel
open scoped Classical Topology BigOperators

private theorem relative {x y d ε a σ : ℝ} (sgn : σ=1 ∨ σ= -1) (dp : 0<d)
    (positive : d/2 < σ*y) (err : |x-y| ≤ (ε*d/2)*a) (ep : 0≤ε) (ap : 0≤a) :
    |x/y-1| ≤ ε*a := by
  have room : d/2< |y| := by
    rcases sgn with rfl | rfl
    · exact (by simpa only [one_mul] using positive : d/2<y).trans_le (le_abs_self y)
    · exact (by simpa only [neg_one_mul] using positive : d/2< -y).trans_le (neg_le_abs y)
  have yp : 0< |y| := (half_pos dp).trans room
  rw [div_sub_one (abs_pos.mp yp),abs_div]
  apply (div_le_iff₀ yp).2
  calc
    |x-y| ≤ ε*d/2*a := err
    _ = ε*a*(d/2) := by ring
    _ ≤ ε*a*|y| := mul_le_mul_of_nonneg_left room.le (mul_nonneg ep ap)

theorem at_earlier {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (J:ℝ→tower S) (Z:WilsonPrescription G)
    {H:(Bel R.family.book).Hierarchy} (L:Layout F) {U:Filter (ℕ×ℕ)}
    {δ g:ℝ→ℝ} (coupling:Coupling G g) (D:Profiles R 4) (j:D.probes.index)
    (v₀:(standard R.family.labels).Ref 4)
    (hs:D.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 v₀)
    (e:ℕ) (deposit:ℝ→RG17.Free R.family 4→R.family.label 4)
    (χ:ℂ→L[ℝ]ℝ) (σ:ℝ) (record:Row (H:=H) (U:=U) F J Z L δ g D j v₀ hs e deposit χ σ) :
    let φ:=WilsonInvariantActionCalibratedColumn.packet v₀ hs (test D j)
    let v:=(Bel R.family.book).project 4 v₀
    let a:=fun r=>deposit r (stepField R.family)
    let b:=fun r=>deposit r (freeInput F J Z 4 r v)
    ∀q:ℕ,∀ε>0,∀ᶠr in trail, let k:=berth R (2*1+q+1+25) (L.level r)
      ∀hr:0<r,∀ᶠz:ℕ×ℕ in U,∃live:k<z.1,
      let marks:=Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (atRef L 4 r z (a r)) (fun _=>atRef L 4 r z (b r))
      let low:=χ (earlier R (per:=z.2) live.le marks (dilate hr φ))
      let stress:=χ (tested (TraceExtension.center F) (homogeneous F J Z r 4 v) r φ)
      low ≠ 0 ∧ |(r^4/(4*δ r))*stress/low - 1| ≤ ε*(g r)^q := by
  intro φ v a b
  let cov:=fun r=>tested (J r 4 (stepField R.family)) (homogeneous F J Z r 4 v) r φ
  let c:=tree (D.probes.shell j) (test D j) H 4 (stepField R.family)
  obtain ⟨polar,sgn,_,dp,_,ward,_,_,prices⟩:=record
  intro q ε ep
  filter_upwards [ward,prices q (ε*|χ c|/2) (by positivity),coupling.positive] with r law ready gp
  let source:=tested (TraceExtension.center F) (homogeneous F J Z r 4 v) r φ
  let t:=r^4/(4*δ r)
  have original : (t:ℂ)*source=cov r := (eq_div_iff law.1).mp law.2
  have measured : t*χ source=χ (cov r) := by
    rw [←original]
    change t • χ source = χ (t • source)
    exact (χ.map_smul t source).symm
  intro k hr
  filter_upwards [ready hr] with z seen
  obtain ⟨live,lift⟩:=seen
  refine ⟨live,?_,?_⟩
  · intro hz
    have positive:=lift.1
    rw [hz,mul_zero] at positive
    exact (not_lt_of_ge (half_pos dp).le) positive
  · rw [measured]
    exact relative sgn dp lift.1 ((component χ polar _ _).trans (by
      rw [norm_sub_rev];exact lift.2.2.1)) ep.le (pow_nonneg gp.le _)

end YM.Integration.WilsonMatrixOriginalLowerWard
