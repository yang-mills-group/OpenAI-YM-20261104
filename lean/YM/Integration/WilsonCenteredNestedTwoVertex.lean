import YM.Integration.WilsonCenteredNestedIntake

/-! A grade-four pair is deposited at the inner vertex. Every component
through the chosen horizon, including its scalar, enters the outer
ordinary packet with the third grade-four field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedTwoVertex
open OPE OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Tree OPE.Nesting.Composite
open Extraction Spec Table Filter WilsonCenteredNestedProgram WilsonCenteredNestedRates
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def pair := fork 2 (fun _=>bud)
def arms : Fin 2 → Tree := ![pair,bud]
def full := fork 2 arms
def dates (r a : ℝ) : full.Inner → ℝ
  | .inl _ => r
  | .inr _ => a
def caps (h d : ℕ) : full.Inner → ℕ
  | .inl _ => h
  | .inr _ => d

private theorem oneInner : Fintype.card pair.Inner = 1 := by
  change Fintype.card (Unit ⊕ Σ _ : Fin 2,Empty) = 1
  simp

private theorem innerSum {M : Type} [AddCommMonoid M] (B : ℝ → M) (r a : ℝ) :
    ∑ j:full.Inner,B (dates r a j) = B r + B a := by
  change (∑ j:(fork 2 arms).Inner,B (dates r a j)) = _
  rw [Tree.sum_inner,Fin.sum_univ_two]
  change B r + ((∑ j:pair.Inner,B a) + ∑ j:Empty,B a) = _
  simp [oneInner]

private theorem innerProd (B : ℝ → ℝ) (r a : ℝ) :
    ∏ j:full.Inner,B (dates r a j) = B r * B a := by
  change (∏ j:(fork 2 arms).Inner,B (dates r a j)) = _
  rw [Tree.prod_inner,Fin.prod_univ_two]
  change B r * ((∏ j:pair.Inner,B a) * ∏ j:Empty,B a) = _
  simp [oneInner]

theorem engineering (v : full.Leaf → S.Tag) (four : ∀ i,(v i).1=4) (r a : ℝ) :
    leaves full (dates r a) (degrees v) r = (r^4*a^8)⁻¹ := by
  have same : degrees v = fun _=>4 := funext four
  rw [same]
  change (∏ i:Fin 2,leaves (arms i) (childAge i (dates r a))
    (childWages i (fun _ : full.Leaf=>4)) r) = _
  rw [Fin.prod_univ_two]
  change (∏ _ : Fin 2,(a^4)⁻¹)*(r^4)⁻¹ = _
  rw [Fin.prod_univ_two,mul_inv_rev]
  have powers : a^8=a^4*a^4 := by ring
  rw [powers,mul_inv_rev]

theorem signedFee (v : full.Leaf → S.Tag) (four : ∀ i,(v i).1=4) (r a : ℝ) (h d : ℕ)
    (L E : ℝ → ℝ) :
    WilsonCenteredNestedPhysical.vertexFee F Q (dates r a) v (caps h d) h L E =
      premium F Q full (caps h d) (dates r a) (fun _=>1) * (L r*L a) *
        (r^h/(r^4*a^8)) * (E r+E a) := by
  change ((premium F Q full (caps h d) (dates r a) (fun _=>1) *
    (∏ i:full.Inner,L (dates r a i))) * r^h * leaves full (dates r a) (degrees v) r) *
    (∑ i:full.Inner,E (dates r a i)) = _
  rw [innerProd L r a,innerSum E r a,engineering v four r a]
  change ((_ * (L r*L a)) * r^h * (r^4*a^8)⁻¹) * (E r+E a) = _
  rw [div_eq_mul_inv,mul_assoc (a:=_ * (L r*L a)) (b:=r^h)]

theorem original (bank : Nesting.Uniform F Q) (A : Rule F Q) (g L : ℝ → ℝ) (Ln : ∀ r,0 ≤ L r)
    (order : ℕ) (v : full.Leaf → S.Tag) (four : ∀ i,(v i).1=4) (h d : ℕ) (c : Q.channels h)
    (M η ε : ℝ) (Mn : 0 ≤ M) (ηp : 0 < η) (ep : 0 < ε)
    (rows : WilsonCenteredNestedIntake.localRows F Q A g L (fun a=>|g a|^order) M η full v (caps h d) h) :
    ∀ᶠ r:ℝ in 𝓝[>]0,∀ (a : ℝ) (z : full.Plot),Accept r M η (dates r a) z →
      ‖Kernel.output F Q z v c - run F Q A g full (dates r a) z v (caps h d) h ⟨Fin.last h,c⟩‖ ≤
        bothToll (wages v) ε h (caps h d) (dates r a) +
        premium F Q full (caps h d) (dates r a) (fun _=>1) * (L r*L a) *
          (r^h/(r^4*a^8)) * (|g r|^order+|g a|^order) := by
  filter_upwards [WilsonCenteredNestedIntake.filed F Q bank A g L Ln order v (caps h d) h c M η ε Mn ηp ep rows]
    with r atRadius
  intro a z geometry
  rw [← signedFee F Q v four r a h d L (fun a=>|g a|^order)]
  exact atRadius _ _ geometry

end YM.Integration.WilsonCenteredNestedTwoVertex
