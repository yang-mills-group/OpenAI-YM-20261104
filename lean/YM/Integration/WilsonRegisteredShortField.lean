import YM.Integration.WilsonRegisteredSoftCovariance

/-! At every original reporting date the complementary small-support observable
is the same deposited primary and the sum of its actual retained masked rows. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonRegisteredShortField
open Lattice RG Wilson Source Push.Local MergeProof PhysicalNext.Repeat.Legato
open WilsonLimitConstruction WilsonInheritedRegisteredField
open scoped Classical
variable {G:Gauge} {C:Family G} (h:C.Makes) {k N per d:ℕ}

def high (hk:k≤N) (v:C.label d) (o:Site (C.side k per)) (b:ℕ) (U:Config G (C.side k per)) : ℂ :=
  alto C.path k d*WilsonDegreeFourInheritedTail.tail h hk v o b U

def short (hk:k≤N) (v:C.label d) (o:Site (C.side k per)) (b:ℕ) (U:Config G (C.side k per)) : ℂ :=
  regular h hk v o U-high h hk v o b U

/-- The support test uses the original radius and the original site. -/
theorem belongs (hk:k≤N) (hr:C.ref d≤k) (v:C.label d) (o:Site (C.side k per)) (b i:ℕ)
    (x:Site (C.side k per)) :
    let Z:=packet h hk v o
    let A:=C.path.rep N per k
    coverNumber A.p.B (Z.support i)<b → x∈Z.support i →
      separation o x≤b*(4*A.p.B+2)+2*A.p.B := by
  intro Z A inside seen
  have prior:=WilsonTranslatedFactory.based h hr hk o ((C.factory d N per).terminal.symm v)
  have marked : Z.Format o C.params A:=prior.1
  exact (Corona.extent _ _ (marked.origin i) seen).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ inside.le) _)

/-- Whole finite-regulator observable, including the constant part, the
original masked primary and every one of the infinitely many admitted rows. -/
theorem filed (hk:k≤N) (hr:C.ref d≤k) (v:C.label d) (o:Site (C.side k per)) (b:ℕ)
    (U:Config G (C.side k per)) :
    let Z:=packet h hk v o
    let A:=C.path.rep N per k
    let S:=C.localSection d
    let L:=C.labels.level d
    short h hk v o b U=alto C.path k d*(Z.x 0+
      masked A.p.threshold (S.footprint o) (S.places (L.scaled A.p.threshold⁻¹ (L.core Z.x)) o) U+
      ∑' i,if coverNumber A.p.B (Z.support i)<b then Z.maskedTerm A i U else 0) := by
  intro Z A S L
  have cash:=WilsonTranslatedFactory.based h hr hk o ((C.factory d N per).terminal.symm v)
  obtain ⟨a,ha,rows⟩:=Coefficient.regular_series cash.2
  have bound (i:ℕ):‖Z.maskedTerm A i U‖≤a i:=rows i U
  have allRows : Summable (fun i=>Z.maskedTerm A i U) :=
    (ha.of_nonneg_of_le (fun i=>norm_nonneg _) bound).of_norm
  have tailRows : Summable (fun i=>if b≤coverNumber A.p.B (Z.support i) then Z.maskedTerm A i U else 0) := by
    apply Summable.of_norm
    refine ha.of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=>?_)
    split
    · exact bound i
    simpa only [norm_zero] using (norm_nonneg _).trans (bound i)
  have pieces:=allRows.tsum_sub tailRows
  have rows_eq : (∑' i,Z.maskedTerm A i U)-
      (∑' i,if b≤coverNumber A.p.B (Z.support i) then Z.maskedTerm A i U else 0)=
       ∑' i,if coverNumber A.p.B (Z.support i)<b then Z.maskedTerm A i U else 0 := by
    rw [←pieces]
    apply tsum_congr
    intro i
    by_cases hb:b≤coverNumber A.p.B (Z.support i)
    · simp only [hb,if_true,Nat.not_lt_of_ge hb,if_false,sub_self]
    simp only [hb,if_false,lt_of_not_ge hb,if_true,sub_zero]
  change alto _ _ _*(Z.x 0+_+(∑' i,Z.maskedTerm A i U)) -
    alto _ _ _*(∑' i,if b≤coverNumber A.p.B (Z.support i) then Z.maskedTerm A i U else 0)=_
  rw [←rows_eq]
  ring

end YM.Integration.WilsonRegisteredShortField
end
