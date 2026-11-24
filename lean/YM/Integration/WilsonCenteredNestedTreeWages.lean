import YM.Integration.WilsonCenteredNestedTreeCourse

/-! The original two-stage branch census and the two different clock fees,
after the exact engineering conversion on all three submitted grades. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedTreeWages
open Function Filter Set Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Prescription
open OPE.Log OPE.Nesting OPE.Nesting.Atom OPE.Nesting.Tree OPE.Nesting.Composite
open WilsonCenteredNestedTwoVertex WilsonCenteredNestedProgram WilsonCenteredNestedTreeSharp
open WilsonCenteredNestedTreeLeaves WilsonCenteredNestedPairChord WilsonCenteredNestedPairRead
open WilsonCenteredNestedRates WilsonCenteredNestedIntake WilsonCenteredNestedGross
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

private lemma one : Fintype.card pair.Inner=1 := by
  change Fintype.card (Unit ⊕ Σ _:Fin 2,Empty)=1
  simp

lemma two_sum (E:ℝ→ℝ) (a r:ℝ) : ∑i:full.Inner,E (dates r a i)=E r+E a := by
  change (∑i:(fork 2 arms).Inner,E (dates r a i))=_
  rw [Tree.sum_inner,Fin.sum_univ_two]
  change E r + ((∑ _:pair.Inner,E a) + ∑ _:Empty,E a)=_
  simp [one]

lemma two_prod (L:ℝ→ℝ) (a r:ℝ) : ∏i:full.Inner,L (dates r a i)=L r*L a := by
  change (∏i:(fork 2 arms).Inner,L (dates r a i))=_
  rw [Tree.prod_inner,Fin.prod_univ_two]
  change L r * ((∏ _:pair.Inner,L a) * ∏ _:Empty,L a)=_
  simp [one]

lemma leaf_wage (v:full.Leaf→S.Tag) (a r:ℝ) :
    leaves full (dates r a) (degrees v) r = (a^((near v 0).1+(near v 1).1)*r^(other v).1)⁻¹ := by
  change (∏i:Fin 2,leaves (arms i) (childAge i (dates r a)) (childWages i (degrees v)) r)=_
  rw [Fin.prod_univ_two]
  change (∏i:Fin 2,(a^(near v i).1)⁻¹)*(r^(other v).1)⁻¹ = _
  rw [Fin.prod_univ_two,pow_add]
  simp only [mul_inv_rev]
  ring

lemma units (v:full.Leaf→S.Tag) (m:ℕ) {a r:ℝ} (ap:0<a) (rp:0<r) :
    charge v m a r * (r^m * leaves full (dates r a) (degrees v) r) = 1 := by
  rw [leaf_wage]
  change (a^((near v 0).1+(near v 1).1)*r^(other v).1/r^m)*(r^m*(a^((near v 0).1+(near v 1).1)*r^(other v).1)⁻¹)=1
  field_simp

lemma census (m D:ℕ) (a r:ℝ) :
    premium F Q full (caps m D) (dates r a) (fun _=>1) = Fintype.card (Menu.Cut Q D) := by
  change (Fintype.card (Branches F Q (f:=arms) (rollCaps (caps m D))):ℝ) *
    ((∏i:Fin 2,premium F Q (arms i) (childAge i (caps m D)) (childAge i (dates r a)) (fun _=>1))*1)=_
  rw [Fintype.card_congr (branches F Q m D),Fin.prod_univ_two]
  change _ * ((((Fintype.card (Fin 2→Unit):ℝ)*((∏_:Fin 2,(1:ℝ))*1)) * 1) * 1)=_
  simp

theorem original (A:Rule F Q) (g L:ℝ→ℝ) (ln:∀x,0≤L x) (p:ℕ) (v:full.Leaf→S.Tag) (D m:ℕ)
    (c:Q.channels m) {M η:ℝ} (rows:localRows F Q A g L (fun x=>|g x|^p) M η full v (caps m D) m) :
    ∀ᶠr:ℝ in 𝓝[>]0,∀(a:ℝ)(z:full.Plot),Accept r M η (dates r a) z→
      charge v m a r * ‖Kernel.chord F Q z v c (caps m D)-run F Q A g full (dates r a) z v (caps m D) m ⟨Fin.last m,c⟩‖ ≤
      Fintype.card (Menu.Cut Q D)*(L r*L a)*(|g r|^p+|g a|^p) := by
  filter_upwards [WilsonCenteredNestedIntake.original F Q A g L (fun x=>|g x|^p) M η full v (caps m D) m rows]
    with r table a z ok
  have rp:0<r:=ok.levels.1
  have ap:0<a:=(ok.levels.2.2 (0:Fin 2)).1
  have qn:0≤charge v m a r := by unfold charge WilsonCenteredNestedTreeWallet.toll;positivity
  have sub := (WilsonCenteredNestedCalibration.original F Q A g L (fun x=>|g x|^p) ln (fun _=>pow_nonneg (abs_nonneg _) _)
    full (dates r a) z v (caps m D) m ⟨Fin.last m,c⟩ r rp ok.levels (table _ _ ok.levels ok.relative)).change
  erw [WilsonCenteredNestedProgram.chord F Q g (dates r a) z v (caps m D) m c,WilsonCenteredNestedRates.separated] at sub
  change _ ≤ (((premium F Q full (caps m D) (dates r a) (fun _=>1) * (∏i:full.Inner,L (dates r a i))) * r^m) *
    leaves full (dates r a) (degrees v) r) * (∑i:full.Inner,|g (dates r a i)|^p) at sub
  erw [two_prod L a r,two_sum (fun x=>|g x|^p) a r,census F Q m D a r] at sub
  have receipt:=mul_le_mul_of_nonneg_left sub qn
  apply receipt.trans_eq
  calc
    _ = (charge v m a r * (r^m * leaves full (dates r a) (degrees v) r)) *
      (Fintype.card (Menu.Cut Q D)*(L r*L a)*(|g r|^p+|g a|^p)) := by ring
    _ = _ := by rw [units _ m ap rp,one_mul]

end YM.Integration.WilsonCenteredNestedTreeWages
