import YM.Integration.WilsonConditionalTaylorThermalStencil
import YM.RGComparison.Core16.Spool.Beacon

/-! Finite signed coefficient inventory for any heterogeneous roster. Repeated
occurrences of the same face or color appear as distinct factors. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonConditionalTaylorThermalCensus
open Function Filter Lattice RG Tree Wilson Labels Source Precision Push.BetaTransport
open RGComparison.Core16 RGComparison.Core16.Descent PertExtension.GaussianScore
open ThermalShortcuts.ThermalJets WilsonConditionalTaylorThermalStencil
open scoped Topology Classical BigOperators
variable {G : Gauge} {a b : Side}
variable {I : Type*} [Fintype I] {D : I → ℕ} {F : ∀ i, Frame G (D i)}
    {T : ∀ i, SectionData (F i)} {k : ∀ i, (F i).Index} (S : ∀ i, Stencil (T i) (k i))

abbrev index (i : I) := Fin (S i).arity × G.ColorIndex
abbrev choice := ∀ i, index S i →₀ ℕ
abbrev ticket := Σ i : I, Σ _ : index S i, ℕ

def rows : Finset (choice S) :=
  Fintype.piFinset (fun i => (S i).polynomial.support.filter
    fun m => WilsonConditionalTaylorThermalPolynomial.degree m = ((F i).grades (k i)).2)

def bill (part : Bool) (m : choice S) :=
  Spool.look part (∏ i, MvPolynomial.coeff (m i) (S i).polynomial)

def parties (m : choice S) : Finset (ticket S) :=
  Finset.univ.sigma (fun i => (m i).support.sigma fun j => Finset.range (m i j))

def face (o : I → Site a) (r : ticket S) : Face (Per a) :=
  Work.F03.slotFace ((S r.1).slot r.2.1.1) (o r.1)

def color (r : ticket S) : G.ColorIndex := r.2.1.2

theorem size {m : choice S} (hm : m ∈ rows S) :
    (parties S m).card = ∑ i, ((F i).grades (k i)).2 := by
  have h := Fintype.mem_piFinset.mp hm
  simp only [parties,Finset.card_sigma,Finset.card_range]
  exact Finset.sum_congr rfl fun i _ => (Finset.mem_filter.mp (h i)).2

theorem polynomial (d : Descent a b) (o : I → Site a) (part : Bool)
    (x : Coordinates G d) :
    Spool.look part (∏ i, head (S i) d (o i) x) =
      ∑ m ∈ rows S, bill S part m *
        Law.product (fun r => leg G d (face S o r) (color S r)) (parties S m) x := by
  unfold head WilsonConditionalTaylorThermalPolynomial.entered
  rw [Finset.prod_univ_sum, map_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.prod_mul_distrib]
  have bits :
      (∏ i, WilsonConditionalTaylorThermalPolynomial.monomial (m i)
          (coordinates (S i) d (o i) x)) =
        ((Law.product (fun r => leg G d (face S o r) (color S r)) (parties S m) x : ℝ) : ℂ) := by
    simp only [WilsonConditionalTaylorThermalPolynomial.monomial,coordinates,Law.product,
      parties,Finset.prod_sigma,face,color,Finset.prod_const,Finset.card_range,
      Complex.ofReal_prod,Complex.ofReal_pow]
  rw [bits, mul_comm,← Complex.real_smul, map_smul, smul_eq_mul, mul_comm]
  rfl

end YM.Integration.WilsonConditionalTaylorThermalCensus
