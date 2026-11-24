import YM.Integration.WilsonOriginalNullCorridor

/-! Trace a physical null source through an arbitrary finite chain of its
actual affine ancestors. Each emitted local section is retained at its own
date and transported by the literal Wilson conditional operators. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullHistory
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext Repeat Legato Graces Roost Org Push.Local
open WilsonOriginalNullCorridor WilsonOriginalNullFiledStep
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius
variable {G:Gauge} (C:Family G) (d N p b:ℕ) (W:∀ j,Rep G (C.side j p))
    (o:∀ j,Site (C.side j p)) (ε:ℝ)
local notation "F₀" => C.labels.level d
local notation "S₀" => C.localSection d
local notation "κ" j:max => LocalComparison.forcedDivisor C j
local notation "emit" j:max x:max => (primary (o (b+j)) x).density (o (b+j)) S₀ (W (b+j))
local notation "raw" j:max z:max => Coefficient.density z (o (b+j)) S₀ (W (b+j))

/-- The physical post realizing each `Filed` is `FiledStep.original`. Each
finite sum below is linear at the original density before any test is read. -/
theorem finite : ∀ n:ℕ,
    (∀ j<n, o (b+j)=(C.path.levels.clock.op (b+j) p).ratio.parent (o (b+j+1))) →
    (∀ j<n, ∃ A B D Δ w:ℝ,(W (b+j)).Lawful A B D Δ w) →
    (∀ j<n,Filed C d N p (b+j) W (o (b+j+1)) ε) →
    ∀ (h:Coefficient F₀ (C.side (b+n) p)) (B:ℝ), h.Format (o (b+n)) C.params (W (b+n)) →
      h.remBound (o (b+n)) (W (b+n)) (κ (b+n)) B → projection F₀ C.params (W (b+n)).p.threshold (o (b+n)) h=0 →
      ∃ (v:Coefficient F₀ (C.side b p)) (α:ℕ→(F₀).Coeff), v.Format (o b) C.params (W b) ∧
        v.remBound (o b) (W b) (κ b) (gain C b (b+n)*B) ∧ projection F₀ C.params (W b).p.threshold (o b) v=0 ∧
        (∀ j<n, (F₀).coeffSize (α j) ≤ ε*gain C (b+j) (b+n)*B) ∧
        flow C d N p b n (raw n h) = v.density (o b) S₀ (W b) +
          ∑ j∈Finset.range n, flow C d N p b j (emit j (α j)) := by
  intro n
  induction n with
  | zero =>
    intro _ _ _ h B form paid null
    exact ⟨h,fun _=>0,form,by simpa only [Nat.add_zero,gain_self,one_mul] using paid,null,
      by simp,by simp [flow]⟩
  | succ n previous =>
    intro route laws filed h B form paid null
    obtain ⟨z,a,zfit,zpaid,clear,aprice,face⟩:=filed n (Nat.lt_succ_self n) h B form paid null
    rw [←route n (Nat.lt_succ_self n)] at zfit zpaid clear face
    let L:ℝ:=(C.S.block (b+n)).val
    let θ:=L^(-(1/8:ℝ))
    have above:0 < L := zero_lt_one.trans_le (GermGraph.factor_positive C (b+n)).le
    obtain ⟨v,α,vfit,vpaid,vclear,record,read⟩ :=
      previous (fun j hj=>route j (Nat.lt_succ_of_lt hj)) (fun j hj=>laws j (Nat.lt_succ_of_lt hj))
        (fun j hj=>filed j (Nat.lt_succ_of_lt hj)) z (θ*B) zfit zpaid clear
    let issued (j:ℕ) := if j=n then a else α j
    refine ⟨v,issued,vfit,?_,vclear,?_,?_⟩
    · have eq:gain C b (b+(n+1))*B = gain C b (b+n)*(θ*B) := by
        rw [show b+(n+1)=b+n+1 by omega,gain_step];dsimp only [θ,L];ring
      exact eq.symm ▸ vpaid
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with older|eqj
      · have old:=record j older
        rw [show issued j=α j from if_neg (Nat.ne_of_lt older)]
        rw [show b+(n+1)=b+n+1 by omega,gain_step];exact old.trans_eq (by dsimp only [θ,L];ring)
      · subst j
        simp only [issued,if_pos rfl]
        rw [show b+(n+1)=b+n+1 by omega,gain_step,gain_self,one_mul]
        have lnz:= (Real.rpow_pos_of_pos above (1/8:ℝ)).ne'
        calc
          _ = (L^(1/8:ℝ))⁻¹*(L^(1/8:ℝ)*(F₀).coeffSize a) := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left aprice (inv_nonneg.mpr (Real.rpow_nonneg above.le _))
          _ = ε*((C.S.block (b+n)).val:ℝ)^(-(1/8:ℝ))*B := by rw [Real.rpow_neg above.le];ring
    · obtain ⟨_,_,_,_,_,law⟩:=laws n (Nat.lt_succ_self n)
      have integrableZ:Integrable (raw n z) (prior G _):=(z.envelope S₀ law zpaid zfit).integrableC _
      have integrableA:Integrable (emit n a) (prior G _):=((primary (o (b+n)) a).envelope S₀ law
        (primary_rem a (show 0 < (1:ℝ) from zero_lt_one)) (primary_format (H:=C.params) a)).integrableC _
      have sums : (∑ j∈Finset.range n,flow C d N p b j (emit j (issued j))) =
          ∑ j∈Finset.range n,flow C d N p b j (emit j (α j)) := by
        apply Finset.sum_congr rfl;intro j hj
        rw [show issued j=α j from if_neg (Nat.ne_of_lt (Finset.mem_range.mp hj))]
      change flow C d N p b n (GermGraph.transition (C:=C) d N p (b+n)
        (h.density (o (b+n+1)) S₀ (W (b+n+1)))) = _
      rw [face,flow_add C d N p b n _ _ integrableZ integrableA,read,Finset.sum_range_succ,sums,
        show issued n=a from if_pos rfl]
      abel

end YM.Integration.WilsonOriginalNullHistory
