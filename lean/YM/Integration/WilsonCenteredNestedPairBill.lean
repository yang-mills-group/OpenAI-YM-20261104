import YM.Integration.WilsonCenteredNestedTwoVertex

/-! Exact powers for the two physically deposited grade-four vertices.
The native spatial term has the child horizon gain (a/r)^(d+1). -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedPairBill
open OPE OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Tree OPE.Nesting.Composite
open Extraction Spec Table Filter WilsonCenteredNestedProgram WilsonCenteredNestedRates
open WilsonCenteredNestedTwoVertex
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def inlet : Σ i,(arms i).Inner := ⟨0,Sum.inl ()⟩

private theorem sole (j : Σ i,(arms i).Inner) : j=inlet := by
  obtain ⟨i,j⟩ := j
  fin_cases i
  · change Unit ⊕ Σ _ : Fin 2,Empty at j
    rcases j with ⟨⟩ | ⟨_,x⟩
    · rfl
    · exact nomatch x
  · exact nomatch j

private theorem allLeaves : Fintype.card full.Leaf = 3 := by
  change Fintype.card (Σ i:Fin 2,(arms i).Leaf) = 3
  rw [Fintype.card_sigma,Fin.sum_univ_two]
  change Fintype.card (Σ _ : Fin 2,Unit) + Fintype.card Unit = 3
  simp

theorem spatial (v : full.Leaf → S.Tag) (four : ∀ i,(v i).1=4) (r a ε : ℝ) (h d : ℕ) :
    bothToll (wages v) ε h (caps h d) (dates r a) =
    r^((h:ℝ)-12-ε) * (a/r)^((-8:ℝ)-ε) * (a/r)^(d+1) := by
  letI : Unique (Σ i,(arms i).Inner) := ⟨⟨inlet⟩,sole⟩
  have loss : (∑ i:full.Leaf,wages v i)=12 := by
    simp only [wages,degrees,four,Finset.sum_const,Finset.card_univ,allLeaves]
    norm_num
  have head : full.headSum (wages v) (.inr inlet)=8 := by
    change (∑ i:(Σ _ : Fin 2,Unit),wages v ⟨0,i⟩)=8
    norm_num [wages,degrees,four,Fintype.sum_sigma,Fin.sum_univ_two]
  have ratio : full.ratios 1 (dates r a) (.inr inlet)=a/r := rfl
  have gain : nestPrice (dates r a) (caps h d) = (a/r)^(d+1) := by
    unfold nestPrice
    rw [Fintype.sum_unique]
    rfl
  have transport : (∏ i : Σ j,(arms j).Inner,
      (full.ratios 1 (dates r a) (.inr i))^(-full.headSum (wages v) (.inr i)-ε)) =
      (a/r)^((-8:ℝ)-ε) := by
    rw [Fintype.prod_unique]
    change (full.ratios 1 (dates r a) (.inr inlet))^(-full.headSum (wages v) (.inr inlet)-ε)=_
    rw [ratio,head]
  change (r^((h:ℝ)-(∑ i:full.Leaf,wages v i)-ε) *
      (∏ i : Σ j,(arms j).Inner,(full.ratios 1 (dates r a) (.inr i))^(-full.headSum (wages v) (.inr i)-ε))) *
      nestPrice (dates r a) (caps h d) = _
  rw [loss,transport,gain]

theorem original (bank : Nesting.Uniform F Q) (A : Rule F Q) (g L : ℝ → ℝ) (Ln : ∀ r,0 ≤ L r)
    (order : ℕ) (v : full.Leaf → S.Tag) (four : ∀ i,(v i).1=4) (h d : ℕ) (c : Q.channels h)
    (M η ε : ℝ) (Mn : 0 ≤ M) (ηp : 0 < η) (ep : 0 < ε)
    (rows : WilsonCenteredNestedIntake.localRows F Q A g L (fun a=>|g a|^order) M η full v (caps h d) h) :
    ∀ᶠ r:ℝ in 𝓝[>]0,∀ (a : ℝ) (z : full.Plot),Accept r M η (dates r a) z →
      ‖Kernel.output F Q z v c - run F Q A g full (dates r a) z v (caps h d) h ⟨Fin.last h,c⟩‖ ≤
      r^((h:ℝ)-12-ε) * (a/r)^((-8:ℝ)-ε) * (a/r)^(d+1) +
      premium F Q full (caps h d) (dates r a) (fun _=>1) * (L r*L a) *
        (r^h/(r^4*a^8)) * (|g r|^order+|g a|^order) := by
  filter_upwards [WilsonCenteredNestedTwoVertex.original F Q bank A g L Ln order v four h d c M η ε Mn ηp ep rows]
    with r paid
  exact fun a z hz=>(spatial v four r a ε h d ▸ paid a z hz)

end YM.Integration.WilsonCenteredNestedPairBill
