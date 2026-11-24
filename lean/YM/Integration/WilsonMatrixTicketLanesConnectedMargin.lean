import YM.Integration.WilsonMatrixTicketLanesConnectedWard

/-! The intact earlier normalized physical covariance remains nonzero after subtracting the measured fresh block on the same signed test. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesConnectedMargin
open Filter Function Set Finset MeasureTheory Lattice Wilson RG Tree Precision RG17 Source Marker Extraction Extraction.Order Spec
open Table Climb Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS OPE OPE.Therm Next.UVStress Next.Rank.Price
open PhysicalNext.Repeat.Legato SharpGram.Lenses FVA2 FVA2.Register Pert.Asymptotics RGComparison.Core16
open WilsonInvariantActionCapturedProfile WilsonMatrixOriginalReportingMargin
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book} (F:Final R.family f S) (L:Layout F)
  {U:Filter (ℕ×ℕ)}

def Remaining (a b:ℝ→R.family.label 4) (φ:Test 2) (c:ℂ) (χ:ℂ→L[ℝ]ℝ) (σ:ℝ) : Prop :=
  ∀ cap:ℕ,∀ε>0,∀ᶠ r in trail,∀hr:0<r,∀ᶠ z:ℕ×ℕ in U,∃k,∃date:L.level r=k+1,∃future:L.level r<z.1,
    let marks:=Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (atRef L 4 r z (a r)) (fun _=>atRef L 4 r z (b r))
    let old:=earlier R (per:=z.2) future.le marks (dilate hr φ)
    ∀u:Directions G (R.family.side k z.2),(∀i,‖u i‖ ≤ (cap:ℝ)+1) →
      let fresh:=WilsonMatrixTicketLanesConnectedSigned.tested R F L 4 4 a b hr φ date (p:=z.2) future.le u
      ‖old-fresh-c‖ ≤ ε ∧ |χ c|/4 < σ*χ (old-fresh)

/-- Both quantities are evaluated before taking the regulator and radius limits. -/
theorem from_row (g:ℝ→ℝ) (a b:ℝ→R.family.label 4) (φ:Test 2) (c:ℂ) (χ:ℂ→L[ℝ]ℝ) (σ:ℝ)
    (phase:χ=Complex.reCLM ∨ χ=Complex.imCLM) (sign:σ=1 ∨ σ= -1) (nonzero:0 < |χ c|)
    (earns:LeadingRow (U:=U) F L a b φ c χ σ)
    (spend:WilsonMatrixTicketLanesConnectedSigned.Negligible R F L U 4 4 g a b φ) : Remaining (U:=U) R F L a b φ c χ σ:=by
  intro cap ε hp
  let η:=min (ε/2) (|χ c|/4)
  have ηp:0<η:=lt_min (half_pos hp) (div_pos nonzero (by norm_num))
  have ηε:η ≤ ε/2:=min_le_left ..
  have ηc:η ≤ |χ c|/4:=min_le_right ..
  have projected (z:ℂ):|χ z| ≤ ‖z‖:=by rcases phase with rfl|rfl;exact Complex.abs_re_le_norm z;exact Complex.abs_im_le_norm z
  have selected (x:ℝ):σ*x ≤ |x|:=by rcases sign with rfl|rfl;simp only [one_mul];exact le_abs_self _;simp only [neg_one_mul];exact neg_le_abs _
  filter_upwards [earns (ε/2) (half_pos hp),spend 0 cap η ηp] with r measured charged
  intro hr
  filter_upwards [measured hr,charged hr] with z prior localCost
  obtain ⟨_,close,margin⟩:=prior
  obtain ⟨k,date,future,invoice⟩:=localCost
  refine ⟨k,date,future,?_⟩
  dsimp only []
  intro u pinned
  let marks:=Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (atRef L 4 r z (a r)) (fun _=>atRef L 4 r z (b r))
  let old:=earlier R (per:=z.2) future.le marks (dilate hr φ)
  let fresh:=WilsonMatrixTicketLanesConnectedSigned.tested R F L 4 4 a b hr φ date (p:=z.2) future.le u
  have localFee:‖fresh‖ ≤ η:=by simpa only [pow_zero,mul_one] using invoice u pinned
  have near:‖old-c‖ ≤ ε/2:=close
  have oriented:|χ c|/2 < σ*χ old:=margin
  change ‖old-fresh-c‖ ≤ ε ∧ |χ c|/4 < σ*χ (old-fresh)
  constructor
  · rw [sub_right_comm];exact (norm_sub_le _ _).trans (by linarith only [near,localFee,ηε])
  · rw [map_sub,mul_sub];have small:=(selected (χ fresh)).trans ((projected fresh).trans (localFee.trans ηc));linarith only [oriented,small]

end YM.Integration.WilsonMatrixTicketLanesConnectedMargin
