import YM.Integration.PhysicalWilsonHotAllowance
import YM.Integration.ActualWilsonAbsoluteTransport
import YM.Integration.OriginalForcedFlat
import YM.Work.E01

/-! Signed first moments on original rooted pressure events and their positive
Wilson transport to every earlier survivor. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.PhysicalWilsonHotIntegral
open Function Filter Set Finset MeasureTheory Lattice Wilson RG OPE.Therm
open IterationFour PhysicalNext.Repeat.Legato Push.AbsoluteSums.Animals
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

def bank (X : Support n) : Finset (Face (Per n)) :=
  (X.biUnion (neighbors 2)) ×ˢ (Finset.univ : Finset PlaqAxes)

theorem card (X : Support n) :
    (bank X).card ≤ X.card * ballCost 2 * Fintype.card PlaqAxes := by
  rw [bank,Finset.card_product,Finset.card_univ]
  apply Nat.mul_le_mul_right
  apply Finset.card_biUnion_le.trans
  calc
    ∑ x∈X,(neighbors 2 x).card ≤ ∑ _x∈X,ballCost 2 :=
      Finset.sum_le_sum fun x _ => neighbors_card 2 x
    _ = _ := by simp

theorem inside (θ : ℝ) (X : Support n) :
    SelectedCofactorAnchoredRegister.hot (G:=G) θ X ⊆ (House.chilly (bank X) θ)ᶜ := by
  rintro U ⟨z,hz,hF⟩ hC
  obtain ⟨p,hp,hbad⟩ := (flags_spec _ _ _).mp hF
  have ha : separation p.1 z≤2 := by
    change z∈(visits p.1 (square p.2.val.1 p.2.val.2)).toFinset at hp
    rw [List.mem_toFinset,square_corners] at hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl
    · simp
    · exact (Work.E01.sep_step_le ..).trans (by decide)
    · exact (separation_triangle _ (p.1+step p.2.val.1) _).trans
        (Nat.add_le_add (Work.E01.sep_step_le ..) (Work.E01.sep_step_le ..))
    · exact (Work.E01.sep_step_le ..).trans (by decide)
    · simp
  apply (not_lt_of_ge (hC p ?_)) hbad
  apply Finset.mem_product.mpr
  exact ⟨Finset.mem_biUnion.mpr ⟨z,hz,(neighbors_mem 2 z p.1).2
    ((separation_comm z p.1).symm ▸ ha)⟩,Finset.mem_univ _⟩

def restricted {E : Set (Config G n)} (c : ℝ) (f : Config G n → ℂ) : Config G n → ℂ :=
  E.indicator fun U => c • f U

theorem bounded {E : Set (Config G n)} (hE : MeasurableSet E) {c B : ℝ} (hc : 0≤c) (hB : 0≤B)
    {f : Config G n → ℂ} (hf : Measurable f) (pay : ∀ U∈E, ‖f U‖≤B) :
    Envelope (restricted (E:=E) c f) ∧
      ∀ U, ‖restricted (E:=E) c f U‖ ≤ E.indicator (fun _ => c*B) U := by
  have hp (U) : ‖restricted (E:=E) c f U‖ ≤ E.indicator (fun _ => c*B) U := by
    by_cases h : U∈E
    · simp only [restricted,Set.indicator_of_mem h,norm_smul,Real.norm_of_nonneg hc]
      exact mul_le_mul_of_nonneg_left (pay U h) hc
    simp [restricted,h]
  have hF : Measurable (fun U : Config G n => c • f U) := hf.const_smul c
  refine ⟨⟨hF.indicator hE,c*B,fun U => (hp U).trans ?_⟩,hp⟩
  by_cases h : U∈E <;> simp [h,mul_nonneg hc hB]

theorem first {E : Set (Config G n)} {μ : Measure (Config G n)} [IsFiniteMeasure μ]
    (hE : MeasurableSet E) {c B : ℝ} (hc : 0≤c) (hB : 0≤B)
    {f : Config G n → ℂ} (hf : Measurable f) (pay : ∀ U∈E, ‖f U‖≤B) :
    ∫ U,‖restricted (E:=E) c f U‖ ∂μ ≤ c*B*μ.real E := by
  obtain ⟨⟨hM,b,hb⟩,hp⟩ := bounded hE hc hB hf pay
  have hi : Integrable (restricted (E:=E) c f) μ :=
    Integrable.of_bound hM.aestronglyMeasurable b (ae_of_all _ hb)
  apply (integral_mono hi.norm ((integrable_const (c*B)).indicator hE) hp).trans_eq
  rw [integral_indicator hE,setIntegral_const]
  simp [smul_eq_mul,mul_comm]

variable (R : Run G) (hG : G.Simple) (Y : Poetry R.family.path.levels)
local notation "H" => R.family.path
local notation "κ" => R.family.path.levels.clock.forcedAllowance
local notation "g" => Pert.Asymptotics.regulatorRun R.family

include hG Y

theorem sites {ρ : ℝ} (hρ : 0<ρ) (q : ℕ) :
    ∀ᶠ k in atTop, ∀ N,k≤N → ∀ per (X : Support (R.family.side k per)),
      (scene H N per k).real (SelectedCofactorAnchoredRegister.hot
        (ρ*(R.family.path.rep N per k).p.threshold) X) ≤
        (X.card * ballCost 2 * Fintype.card PlaqAxes : ℕ) * κ k ^ q := by
  filter_upwards [PhysicalWilsonHotAllowance.faces Y hG R.makes.wilson hρ q] with k h N hN per X
  letI : IsProbabilityMeasure (scene R.family.path N per k) := OPE.Therm.probability (p:=per) R.makes.wilson hN
  apply ((measureReal_mono (inside _ X) (measure_ne_top _ _)).trans (h N hN per (bank X))).trans
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast card X) (pow_nonneg (Real.exp_nonneg _) q)

theorem divided {ρ : ℝ} (hρ : 0<ρ) (Q : ℕ) :
    ∀ᶠ k in atTop, ∀ N,k≤N → ∀ per (X : Support (R.family.side k per)),
      ∀ (E : Set (Config G (R.family.side k per))), MeasurableSet E →
      E⊆SelectedCofactorAnchoredRegister.hot (ρ*(R.family.path.rep N per k).p.threshold) X →
      ∀ q≤Q, ∀ B, 0≤B → ∀ f : Config G (R.family.side k per) → ℂ, Measurable f →
        (∀ U∈E,‖f U‖≤B) → ∀ j (hj : j≤k),
        ∫ U,‖actualTransport R.family (N:=N) (p:=per)
          (restricted (E:=E) ((Real.sqrt (κ k))^q)⁻¹ f) hj U‖ ∂scene H N per j ≤
          B * (X.card * ballCost 2 * Fintype.card PlaqAxes : ℕ) * κ k := by
  filter_upwards [sites R hG Y hρ (Q+1)] with k h N hN per X E hE hX q hq B hB f hf pay j hj
  letI : IsProbabilityMeasure (scene R.family.path N per k) := OPE.Therm.probability (p:=per) R.makes.wilson hN
  have hw : 0<κ k := Real.exp_pos _
  have hw₁ : κ k≤1 := by
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_nonneg _) _)
  let u := Real.sqrt (κ k)
  have hu : 0<u := Real.sqrt_pos.2 hw
  have hu₁ : u≤1 := by simpa [u] using Real.sqrt_le_sqrt hw₁
  let c := (u^q)⁻¹
  have hc : 0≤c := by dsimp [c]; positivity
  let D : ℝ := (X.card*ballCost 2*Fintype.card PlaqAxes : ℕ)
  let P := restricted (E:=E) c f
  have henv : Envelope P := (bounded hE hc hB hf pay).1
  have hm : (scene H N per k).real E ≤ D*κ k^(q+1) :=
    ((measureReal_mono hX (measure_ne_top _ _)).trans (h N hN per X)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hw.le hw₁ (by omega : q+1≤Q+1)) (by positivity))
  have sqr : u*u=κ k := by rw [←sq,Real.sq_sqrt hw.le]
  have hfrac : c*(κ k^(q+1))=κ k*u^q := by
    change (u^q)⁻¹*(κ k)^(q+1)=κ k*u^q
    rw [pow_succ,←sqr, mul_pow]
    field_simp [hu.ne']
  change (∫ U,‖actualTransport R.family (N:=N) (p:=per) P hj U‖ ∂_) ≤ B*D*κ k
  calc
    _ ≤ ∫ U,‖P U‖ ∂scene H N per k := ActualWilsonAbsoluteTransport.first R.family R.makes hN
      (ActualWilsonAbsoluteTransport.weighted R.family R.makes hN henv) hj
    _ ≤ c*B*(scene H N per k).real E := first hE hc hB hf pay
    _ ≤ c*B*(D*κ k^(q+1)) := mul_le_mul_of_nonneg_left hm (mul_nonneg hc hB)
    _ = B*D*(κ k*u^q) := by rw [←hfrac]; ring
    _ ≤ B*D*(κ k*1) := by
      apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_one₀ hu.le hu₁) hw.le)
      exact mul_nonneg hB (by positivity)
    _ = _ := by rw [mul_one]

/-- The original rate is uniform through every earlier physical read. The
support bill and the true signed amplitude may each depend on the datum. -/
theorem all_orders {ρ C ε : ℝ} (hρ : 0<ρ) (hC : 0≤C) (hε : 0<ε) (a d Q : ℕ) :
    ∀ᶠ k in atTop, ∀ N,k≤N → ∀ per (X : Support (R.family.side k per)),
      ∀ (E : Set (Config G (R.family.side k per))), MeasurableSet E →
      E⊆SelectedCofactorAnchoredRegister.hot (ρ*(R.family.path.rep N per k).p.threshold) X →
      ∀ q≤Q, ∀ B, 0≤B →
      B*(X.card*ballCost 2*Fintype.card PlaqAxes : ℕ)≤C/(g N per k)^d →
      ∀ f : Config G (R.family.side k per) → ℂ, Measurable f → (∀ U∈E,‖f U‖≤B) →
      ∀ j (hj:j≤k),
      ∫ U,‖actualTransport R.family (N:=N) (p:=per)
        (restricted (E:=E) ((Real.sqrt (κ k))^q)⁻¹ f) hj U‖ ∂scene H N per j ≤
          ε*(g N per k)^a := by
  let δ := ε/(C+1)
  have hδ : 0<δ := div_pos hε (by linarith)
  have small : C*δ ≤ ε := by
    have h : (C+1)*δ=ε := by dsimp [δ];field_simp [show C+1≠0 by linarith]
    linarith
  filter_upwards [divided R hG Y hρ Q,OriginalForcedFlat.allowance R hG (a+d) hδ] with
    k raw flat N hN per X E hE hX q hq B hB fee f hf paid j hj
  have hg : 0<g N per k := Currency.g_pos R.makes N per k hN
  change (∫ U,‖actualTransport R.family (N:=N) (p:=per) _ hj U‖ ∂_)≤_
  refine (raw N hN per X E hE hX q hq B hB f hf paid j hj).trans ?_
  calc
    _ ≤ (C/(g N per k)^d)*κ k := mul_le_mul_of_nonneg_right fee (Real.exp_nonneg _)
    _ ≤ (C/(g N per k)^d)*(δ*(g N per k)^(a+d)) :=
      mul_le_mul_of_nonneg_left (flat N per hN) (div_nonneg hC (pow_nonneg hg.le _))
    _ = (C*δ)*(g N per k)^a := by rw [pow_add]; field_simp
    _ ≤ ε*(g N per k)^a := mul_le_mul_of_nonneg_right small (pow_nonneg hg.le _)

end YM.Integration.PhysicalWilsonHotIntegral
end
