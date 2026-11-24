import YM.Integration.FVA1Physical.Round2.IndependentWordBanks
import YM.Integration.FVA1Physical.Round2.FieldWordDegrees
import YM.Integration.FVA1Physical.Round2.SpatialFieldPrice

/-! Lower a complete high-order norm estimate to the requested Wilson
truncation. Every coordinate word may be tested at its own background.
The size of the torus does not enter the interpolation cost. -/
set_option autoImplicit false
set_option maxHeartbeats 950000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Finset Lattice RG YM.Wilson Precision MvPolynomial
open MSbar MSbar.Cacao MSbar.Whisk MSbar.CrossH MSbar.Lis MSbar.Mosaic MSbar.Bakery.Film
open MSbar.Heath MSbar.Rolling RGComparison.Core16.Spool Push.Uniform
open YM.Integration.FVA1Physical.Wilson
open scoped Classical BigOperators Topology

theorem rendered_budget {σ:Type} [Fintype σ] [DecidableEq σ] {c:Side} (loc:σ→Site c)
    (b:Site c) (s q P:ℕ) (F:PowerSeries (Pot σ)) {a H g:ℝ} (hg:0≤g) (unit:g≤1)
    (rows:∀ i≤P,Vault loc {b} a s q 0 (PowerSeries.coeff i F) H) :
    Vault loc {b} a s q 0 (renderedPolynomial F P g) (((P+1:ℕ):ℝ)*H) := by
  have paid:=Quote.total (fun i:ℕ=>g^i • PowerSeries.coeff i F) (range (P+1)) (fun _=>H) (by
    intro i hi
    have input:=rows i (Nat.lt_succ_iff.mp (mem_range.mp hi))
    apply Quote.widen (Quote.mulR input (g^i)) _ le_rfl
    rw [abs_of_nonneg (pow_nonneg hg _)]
    exact mul_le_of_le_one_left input.1 (pow_le_one₀ hg unit))
  simpa only [renderedPolynomial,sum_const,card_range,nsmul_eq_mul] using paid

def fieldKernel (G:Gauge) (a:ℝ) : ℝ :=
  (Fintype.card (Exterior.TypeFace 1)*(Fintype.card G.ColorIndex:ℝ))*((2*(⌈a⁻¹⌉₊:ℝ)+1)^4*meter 1)

theorem raised_field_rooted {G:Gauge} (A:Issue G) (χ:ChartRatio G) (src:PowerSeries (Pot (Joint A.F G)))
    (kind:Kind A.T) (pd:(mold A.pre A.F A.v).PosDef) (b:Site A.c) (p d s q h:ℕ)
    (f:Positions (Primary A.c G)→ℝ) (Z:List (Primary A.c G)→Positions (Primary A.c G))
    {a D H M ε τ:ℝ} (ha:0<a) (hD:0≤D) (hε:0≤ε) (hτ:0<τ) (hg:0≤A.fClock) (unit:A.fClock≤1)
    (inside:∀ l,‖Z l‖≤D) :
    let loc:=Measuring.chart A.c G
    let high:=emittedRows A χ src (p+d)
    let low:=emittedRows A χ src p
    let P:=renderedPolynomial high (p+d) A.fClock
    let Q:=renderedPolynomial low p A.fClock
    let strong:=((q:ℝ)+2)*a
    (∀ i≤p+d,(PowerSeries.coeff i high).totalDegree≤h) →
    (∀ i≤p+d,Vault loc {b} strong (s+s) h 0 (PowerSeries.coeff i high) H) →
    (∀ i : ℕ, p < i → i ≤ p+d → Vault loc {b} a s h 0 (PowerSeries.coeff i high) H) →
    (∀ l,l.length=q → |buoy f (Z l) l-buoy (clue P) (Z l) l|≤ε) →
    fieldCharge loc b strong (s+s) q Z f ≤ M →
    fieldDistance loc b a s q Z f (clue Q) ≤
      τ*(M+(((p+d+1:ℕ):ℝ)*H)*(1+D)^(h+1))+(ε/τ)*(fieldKernel G a)^q+
      ((d:ℝ)*A.fClock^(p+1)*H)*(1+D)^(h+1) := by
  intro loc high low P Q strong degrees rows trunc points actual
  have same:Lap p high low:=emitted_prefix A χ src kind pd (Nat.le_add_right ..)
  have hp:P.totalDegree≤h:=rendered_degree high (p+d) h A.fClock degrees
  have hq:Q.totalDegree≤h:=by
    apply rendered_degree low p h A.fClock
    intro i hi
    rw [←same i hi]
    exact degrees i (hi.trans (Nat.le_add_right ..))
  have difference:(P-Q).totalDegree≤h:=(MvPolynomial.totalDegree_sub ..).trans (max_le hp hq)
  have strong0 : 0 ≤ strong := mul_nonneg (by positivity) ha.le
  have priced:=rendered_budget loc b (s+s) h (p+d) high hg unit rows
  have formal:=polynomial_charge loc b strong0 hD (s+s) h q P hp priced Z inside
  have discarded:=represented_truncation loc {b} 0 s h p d high low hg unit same trunc
  have tail:=polynomial_tail_charge loc b ha.le hD s h q P Q difference discarded Z inside
  exact high_to_low_rooted loc b ha.le hε hτ s q Z f (clue P) (clue Q) points actual formal tail
    (primary_radial_price G ha b)

end YM.Integration.FVA1Physical.Round2.Curvature
