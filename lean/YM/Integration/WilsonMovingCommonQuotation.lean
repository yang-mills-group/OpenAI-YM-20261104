import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Hiring

/-! The two support exponents are quoted on the same physical programs before any block size.
Their common price pays the actual signed singleton return at either exponent. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir.Suite.WilsonCommonQuotation
open Filter Function Set Lattice Wilson Pressure RG Tree Precision Next Next.SectorChange Rows Exterior Bloch
    Planned.AtomRegular MeasureTheory AnalyticBridge.LocalGaussian Push.PriceCompiler Supply Testing AnalyticBridge.LocalGaussianLaws
    AnalyticBridge.VerifiedReset.Time
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}

theorem price_mono {n p r : ℕ} {C : Libretto G n} {A t v w : ℝ}
    (quote : Release.Quotation C p r A t v) (h : v ≤ w) : Release.Quotation C p r A t w := by
  refine ⟨quote.nonneg.trans h, ?_⟩
  intro c f S D P B X Y u x hp ha accepts walled radius cover threshold hu plented τ hτ
  refine (quote.prices S D P B X Y u x hp ha accepts walled radius cover threshold hu plented τ hτ).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (by positivity))
    (mul_nonneg (Real.exp_nonneg _) hτ)

theorem original (s : Sheet G) (K : MapPrices) (r : ℕ → ℕ → ℕ) (t₀ t₁ : ℕ → ℕ → ℝ)
    (ht₀ : ∀ j i, 0 ≤ t₀ j i) (ht₁ : ∀ j i, 0 ≤ t₁ j i) :
    ∃ (f : ℕ → ℕ) (C : Programs s) (v : ℕ → ℕ → ℝ), s.floorL ≤ f ∧
      ∀ g, f ≤ g → Earlier {s with floorL := g} K C v t₀ r ∧
        Earlier {s with floorL := g} K C v t₁ r := by
  obtain ⟨f,C,v₀,hf,lo⟩ := earlier s K r t₀ ht₀
  choose v₁ hi using fun j i => Release.quoting (C j i) (s.profile i).power (r j i)
    (s.profile j).price_pos (ht₁ j i)
  let v (j i : ℕ) := max (v₀ j i) (v₁ j i)
  obtain ⟨F,_,hf',bill⟩ := collect_upper f (fun j L => ∀ i, StepStages j i →
    20 * Release.base (t₁ j i) (r j i) ≤ (L:ℝ) * (s.profile j).supportExponent ∧
      8 * v j i ≤ credit G (s.profile i) * L) (fun j => eventually_transitions j _ _ (fun i _ => by
    have hv := tendsto_natCast_atTop_atTop (R:=ℝ)
    exact ((hv.atTop_mul_const (s.profile j).price_pos).eventually_ge_atTop _).and
      ((hv.const_mul_atTop (credit_pos G (s.profile i))).eventually_ge_atTop _)))
  refine ⟨F,C,v,hf.trans hf',?_⟩
  intro g hg
  have original := lo g (hf'.trans hg)
  have pre : Pre {s with floorL := g} v := fun j i st => (bill j (g j) (hg j) i st).2
  refine ⟨{ original with agrees := fun j i => ⟨(original.agrees j i).1, (original.agrees j i).2.1,
        price_mono (original.agrees j i).2.2 (le_max_left ..)⟩, pre := pre },
    ⟨fun j i => ⟨(original.agrees j i).1, (original.agrees j i).2.1,
        price_mono (hi j i) (le_max_right ..)⟩, original.matins, ?_, pre⟩⟩
  intro j i L st hl
  exact ⟨(bill j L.val ((hg j).trans hl) i st).1,(original.gates j i L st hl).2⟩

end YM.PhysicalNext.JointLoad.Heir.Suite.WilsonCommonQuotation
end
