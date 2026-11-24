import YM.Integration.WilsonOriginalPublicRelativeGramInverse

/-! Two separately dated columns of one public frame enter the same reflected
Wilson form. A finite determining panel therefore has a single extraction for
its full reference square and its cross readings. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramPanel
open Filter Function Finset Lattice Wilson RG Source Labels Cells
open PhysicalNext.Repeat.Legato Extraction Extraction.Banks RG17 Spec Table Table.Pairing
open WilsonOriginalBlissSimultaneousGram
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
  {H:(Climb.Bel R.family.book).Hierarchy}{ℓ:Ultrafilter (ℕ×ℕ)}
  (arch:Trace.Terrace.Arch R.family)(bliss:Trace.Pilot.Bliss F ℓ arch H)
  (J:ℝ→PhysMS.tower S)(level:ℝ→ℕ)(shift:∀d,ℝ→R.family.label d ≃ₗ[ℂ] R.family.label d)
  {I:Type}[Fintype I](a:Axis)(d:I→ℕ)(w:(i:I)→(Spin.comparator R.family.book).Field (d i))
  (φ:I→Test 1)(supports:∀ i,∀x∈tsupport (φ i),Points.allAbove a 0 x)

def before (r s:ℝ)(z:ℕ×ℕ):Matrix I I ℂ:=fun i j=>
  Cells.form (R.family.beta z.1 z.2) (plane R.family z.1 z.2 a)
    (field R F arch level shift (d j) s (φ j) z (J s (d j) (w j)))
    (field R F arch level shift (d i) r (φ i) z (J r (d i) (w i)))

def measured (r s:ℝ):Matrix I I ℂ:=fun i j=>
  WilsonOriginalBlissMixedGram.price R a (d i) (d j) (φ i) (φ j) (supports i) (supports j)
    (J r (d i) (w i)) (J s (d j) (w j))

theorem entry_bound {E:Matrix I I ℂ}(cash:I→I→ℝ)(paid:∀i j,‖E i j‖ ≤ cash i j):
    ‖E‖ ≤ ∑i,∑j,cash i j:=by
  rw [Matrix.linfty_opNorm_def]
  have maxrow:(Finset.univ.sup fun i=>∑j,‖E i j‖₊) ≤ ∑i,∑j,‖E i j‖₊:=
    Finset.sup_le fun i _=>Finset.single_le_sum (f:=fun k:I=>∑j,‖E k j‖₊) (fun _ _=>bot_le) (Finset.mem_univ i)
  have total:(↑(Finset.univ.sup fun i=>∑j,‖E i j‖₊):ℝ) ≤ ∑i,∑j,‖E i j‖:=by
    simpa only [NNReal.coe_sum,coe_nnnorm] using NNReal.coe_le_coe.mpr maxrow
  exact total.trans (Finset.sum_le_sum fun i _=>Finset.sum_le_sum fun j _=>paid i j)

include bliss in
theorem original (r s:ℝ)(atR:∀i,R.family.ref (d i) ≤ level r)(atS:∀i,R.family.ref (d i) ≤ level s)
    (ε:ℝ)(ep:0<ε):
    ∀ᶠ z:ℕ×ℕ in (ℓ : Filter (ℕ×ℕ)),∀i j,
    ‖before R F arch J level shift a d w φ r s z i j-measured R J a d w φ supports r s i j‖ ≤ ε:=by
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  have conv:=WilsonOriginalBlissMixedGram.original R F arch bliss J level shift a (d i) (d j) r s
    (φ i) (φ j) (supports i) (supports j) (atR i) (atS j)
    (V:=fun _=>J r (d i) (w i)) (W:=fun _=>J s (d j) (w j)) tendsto_const_nhds tendsto_const_nhds
  exact ((Metric.tendsto_nhds.mp conv) ε ep).mono fun z hz=>by simpa only [before,measured,dist_eq_norm] using hz.le

end YM.Integration.WilsonOriginalPublicRelativeGramPanel
