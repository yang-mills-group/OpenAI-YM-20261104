import YM.Integration.WilsonRegisteredAxialConditional
import YM.Integration.WilsonRegisteredConditionalCenter

/-! The full old short row is tested in the actual conditional covariance.
Both singletons retain their original normalization at the held field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredAxialCovariance
open MeasureTheory ProbabilityTheory Filter Lattice RG Wilson OPE.Therm RG16 PhysicalNext.Repeat.Legato MSbar.Heath
open WilsonReportingForestAngularReflection WilsonInheritedRegisteredField WilsonRegisteredFrozenReading
open scoped Classical Topology
variable {G:Gauge}
variable (R:Run G)
local notation "A" => R.family.path.levels
local notation "β" => R.family.path.levels.clock.hatBeta

theorem measured (simple:G.Simple) (gate:posted R)
    (slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda (A) m))
    (J:Voice G) (clear:Clear G J) (a:Lattice.Order) (p base t:ℕ) {ε:ℝ} (he:0<ε):
    ∀ᶠ m:ℕ in atTop,∀ N per (live:m<N) d (_ref:R.family.ref d ≤ m+1)
      (v:R.family.label d) (o:Site (R.family.side (m+1) per))
      (B:Config G (R.family.side (m+1) per) → ℂ),
      let k:=m+1
      let Z:=packet R.makes live v o
      let L:=R.family.labels.level d
      let F:=previous R live v o (WilsonDegreeFourInheritedRange.height R p k)
      let E:=actualAverage R.family (N:=N) (p:=per) (m:=m) (E:=ℂ)
      Envelope B →
        (∫V,‖E (fun U=>B U*F U) V-E B V*E F V‖ ∂scene R.family.path N per m)*(Real.log (β k))^t ≤
        Real.sqrt (∫U,‖B U‖^2 ∂scene R.family.path N per k)*(ε*L.coeffSize (L.core Z.x)):=by
  filter_upwards [WilsonRegisteredAxialConditional.measured R simple gate slow J clear a p base t he] with m invoice
  intro N per live d ref v o B k Z L F E hB
  let H:=fun w:Config G (R.family.side m per) × Config G (R.family.side k per)=>B w.2-E B w.1
  have income:=WilsonRegisteredConditionalCenter.income R.family R.makes live B hB
  have gross:=WilsonRegisteredAxialMass.gross R live ref v o (WilsonDegreeFourInheritedRange.height R p k)
  have hF:Envelope F:=⟨gross.1,_,gross.2⟩
  have q:=invoice N per live d ref v o H income.1
  have identification (V):E (fun U=>H (V,U)*F U) V=E (fun U=>B U*F U) V-E B V*E F V:=
    WilsonRegisteredConditionalCenter.covariance R.family R.makes live B F hB hF V
  change (∫V,‖E (fun U=>H (V,U)*F U) V‖ ∂scene R.family.path N per m)*(Real.log (β k))^t ≤ _ at q
  simp_rw [identification] at q
  exact q.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt income.2) (mul_nonneg he.le (Finset.sum_nonneg fun _ _=>norm_nonneg _)))

end YM.Integration.WilsonRegisteredAxialCovariance
