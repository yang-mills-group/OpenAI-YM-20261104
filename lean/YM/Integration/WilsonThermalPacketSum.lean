import YM.Integration.WilsonCurvatureRankBudget

/-! The weighted absolute price of the signed physical read of all native tokens above a fixed curvature rank. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermalPacketSum
open MeasureTheory Filter Set Finset Lattice Wilson RG Marker OPE.Therm
open Comparison.Density.RenderM LocalComparison LocalComparison.MarkedPackets Push.AbsoluteSums
open scoped Classical BigOperators Topology

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] [Fintype V]
variable {R : Census V} {D : V → ComparisonDensity.Address.Orbit}
variable (P : MarkedPackets D G n R) (w : V → ℝ) (g : ℝ) (x : IndependentTests D)

def entry (c : ℕ) (i : ℕ) (U : Config G n) : ℝ :=
  if c ≤ P.rank i then Poly.toll w (P.mode i) * ‖P.term (testInclusion D x) g U i‖ else 0

def token (c : ℕ) (i : ℕ) (U : Config G n) : Poly R :=
  if c ≤ P.rank i then Poly.send (P.mode i) (P.term (testInclusion D x) g U i) else 0

def high (c : ℕ) (U : Config G n) : Poly R := ∑' i, token P g x c i U

def cost (c cap marks : ℕ) (t δ budget : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc c cap, (marks:ℝ)*((t^q+2^q*((q:ℝ)*δ))*budget)

variable {P w g} {width budget : ℝ} {p : BudgetPoint} {address : V → Support n}
variable {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
variable {coverOffset coverSlope : ℕ}
variable (H : P.Paid p address region w g width budget coverOffset coverSlope)

omit [Fintype V] in
theorem scalar (c i : ℕ) (U : Config G n) :
    Poly.price w (token P g x c i U) = entry P w g x c i U := by
  by_cases h : c ≤ P.rank i <;> simp [entry,token,h]

omit [Fintype V] in
theorem entry_cont (c i : ℕ) : Continuous (entry P w g x c i) := by
  unfold entry
  by_cases h : c ≤ P.rank i
  · simp only [if_pos h]
    cases hp : P.packet i with
    | none =>
      simp only [MarkedPackets.term,hp,norm_zero,mul_zero]
      exact continuous_const
    | some T =>
      simp only [MarkedPackets.term,hp]
      unfold Token.read Token.touch Slot.atSite expandAt
      fun_prop
  · simp only [if_neg h]
    exact continuous_const

include H in
theorem integrated (μ : Measure (Config G n)) [IsProbabilityMeasure μ] (c cap : ℕ)
    (hcap : P.rankCap ≤ cap) (t δ : ℝ) (ht : 0 ≤ t) (hd : 0 ≤ δ)
    (rare : ∀ z : Face (Per n), μ.real (trigger z t) ≤ δ) :
    SumBudget (fun i => ∫ U, entry P w g x c i U ∂μ) (cost c cap (Fintype.card V) t δ budget) := by
  let b (q : ℕ) (v : V) := WilsonCurvatureRankBudget.invoice P μ w g width x v q
  have hq (q : ℕ) (v : V) : SumBudget (b q v) ((t^q+2^q*((q:ℝ)*δ))*budget) :=
    WilsonCurvatureRankBudget.paid x H v q t δ ht hd rare
  have htotal := budget_over (Finset.Icc c cap) (fun q i => ∑ v, b q v i)
    (fun q => ∑ _v : V, (t^q+2^q*((q:ℝ)*δ))*budget)
    (fun q _ => budget_over Finset.univ (b q) _ (fun v _ => hq q v))
  have nn (i : ℕ) : 0 ≤ ∫ U, entry P w g x c i U ∂μ := by
    apply integral_nonneg
    intro U
    rw [← scalar x c i U]
    exact Poly.nonnegative H.positive _
  have hs := budget_mono htotal nn (fun i => by
    by_cases hi : c ≤ P.rank i
    · cases hp : P.packet i with
      | none =>
        simp only [entry,if_pos hi,MarkedPackets.term,hp,norm_zero,mul_zero,integral_zero]
        exact htotal.1 i
      | some T =>
        obtain ⟨v,hv⟩ : (P.mode i).val.Nonempty := Finset.nonempty_iff_ne_empty.mpr
          (fun hn => P.marked i T hp (Subtype.ext hn))
        have hr := (P.rank_bounded i T hp).trans hcap
        have hE : 1 ≤ Real.exp (width*T.fall) :=
          Real.one_le_exp (mul_nonneg H.width_pos.le (Nat.cast_nonneg _))
        have hm : 0 ≤ ∫ U, ‖P.term (testInclusion D x) g U i‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
        calc
          _ ≤ b (P.rank i) v i := by
            simp only [b,entry,hi,if_true,integral_const_mul,WilsonCurvatureRankBudget.invoice,hv,eq_self,and_self,hp]
            exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (Poly.worth H.positive _).le hE) hm
          _ ≤ ∑ j, b (P.rank i) j i :=
            Finset.single_le_sum (fun j _ => (hq _ j).1 i) (Finset.mem_univ v)
          _ ≤ _ := Finset.single_le_sum (fun q _ => Finset.sum_nonneg fun j _ => (hq q j).1 i)
            (Finset.mem_Icc.mpr ⟨hi,hr⟩)
    · simp only [entry,if_neg hi,integral_zero]
      exact htotal.1 i)
  simpa only [cost,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hs

include H in
theorem at_field (c cap : ℕ) (hcap : P.rankCap ≤ cap) (U : Config G n) :
    SumBudget (fun i => entry P w g x c i U) (cost c cap (Fintype.card V) 2 0 budget) := by
  have hE (z : Face (Per n)) : (trigger z 2 : Set (Config G n)) = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr (fun _ h => (not_lt_of_ge (G.chord_le_two _)) h)
  simpa only [integral_dirac] using integrated x H (Measure.dirac U) c cap hcap 2 0
    (by norm_num) le_rfl (fun z => by simp [hE z])

include H in
theorem dominated (μ : Measure (Config G n)) [IsProbabilityMeasure μ] (c cap : ℕ)
    (hcap : P.rankCap ≤ cap) (t δ : ℝ) (ht : 0 ≤ t) (hd : 0 ≤ δ)
    (rare : ∀ z : Face (Per n), μ.real (trigger z t) ≤ δ) :
    ∀ (F : Config G n → ℝ) (K : ℝ), 0 ≤ K → (∀ U, 0 ≤ F U) →
      (∀ U, F U ≤ K*(∑' i, entry P w g x c i U)) →
      (∫ U, F U ∂μ) ≤ K*cost c cap (Fintype.card V) t δ budget := by
  intro F K hK hF htest
  let a := entry P w g x c
  let C := cost c cap (Fintype.card V) 2 0 budget
  have point (U : Config G n) : SumBudget (fun i => a i U) C := at_field x H c cap hcap U
  have meas (i : ℕ) := (entry_cont (w:=w) (P:=P) (g:=g) x c i).measurable
  have int (i : ℕ) : Integrable (a i) μ :=
    (integrable_const C).mono' (meas i).aestronglyMeasurable (ae_of_all _ (fun U => by
      rw [Real.norm_of_nonneg ((point U).1 i)]
      exact budget_single (point U) i))
  have hs := integrated x H μ c cap hcap t δ ht hd rare
  have hn : Summable (fun i => ∫ U, ‖a i U‖ ∂μ) := by
    have hnorm (i U) : ‖a i U‖ = a i U := Real.norm_of_nonneg ((point U).1 i)
    simpa only [hnorm] using hs.2.1
  have htone : Integrable (fun U => ∑' i, a i U) μ :=
    (integrable_const C).mono' (Measurable.tsum meas).aestronglyMeasurable (ae_of_all _ (fun U => by
      rw [Real.norm_of_nonneg (tsum_nonneg ((point U).1))]
      exact (point U).2.2))
  calc
    _ ≤ ∫ U, K*(∑' i, a i U) ∂μ := integral_mono_of_nonneg
      (ae_of_all _ hF) (htone.const_mul _) (ae_of_all _ htest)
    _ = K*(∑' i, ∫ U, a i U ∂μ) := by rw [integral_const_mul,←integral_tsum_of_summable_integral_norm int hn]
    _ ≤ _ := mul_le_mul_of_nonneg_left hs.2.2 hK

include H in
theorem price (c cap : ℕ) (hcap : P.rankCap ≤ cap) (U : Config G n) :
    Poly.price w (high P g x c U) ≤ ∑' i, entry P w g x c i U :=
  (Poly.budgeted H.positive (at_field x H c cap hcap U).2.1 (fun i => (scalar x c i U).le)).2

include H in
theorem expected (μ : Measure (Config G n)) [IsProbabilityMeasure μ] (c cap : ℕ)
    (hcap : P.rankCap ≤ cap) (t δ : ℝ) (ht : 0 ≤ t) (hd : 0 ≤ δ)
    (rare : ∀ z : Face (Per n), μ.real (trigger z t) ≤ δ) :
    (∫ U, Poly.price w (high P g x c U) ∂μ) ≤ cost c cap (Fintype.card V) t δ budget := by
  simpa only [one_mul] using dominated x H μ c cap hcap t δ ht hd rare
    (fun U => Poly.price w (high P g x c U)) 1 zero_le_one (fun _ => Poly.nonnegative H.positive _)
    (fun U => by rw [one_mul]; exact price x H c cap hcap U)

end YM.Integration.WilsonThermalPacketSum
end
