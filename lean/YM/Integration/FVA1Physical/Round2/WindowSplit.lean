import YM.Push.LOCAL_SPLITTING.Response

/-! Comparing two independently normalized observations of the same coarse links.
The support and derivative bill use the native masked-density budget. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Function MeasureTheory Lattice Wilson RG Push.Local Push.Local.Kernel Next.Foundations
open scoped Classical
variable {G : Gauge} {c f : Side} (S : StepData c f) (β : ℝ)

private theorem pass_subtract {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (br : S.patch.Branches S.kernel G) (J : Edges c) {F H : Config G f → E}
    (iF : Integrable F (prior G f)) (iH : Integrable H (prior G f)) (U : Config G c) :
    pass S β J (F-H) U = pass S β J F U - pass S β J H U := by
  have integ (Q : Config G f → E) (hQ : Integrable Q (prior G f)) :
      Integrable (fun V => pdf S β J V U • Q V) (prior G f) := by
    unfold pdf; simp_rw [← lifted]; exact slice_int S br hQ _
  unfold pass
  simp only [Pi.sub_apply,smul_sub]
  exact integral_sub (integ F iF) (integ H iH)

private theorem pass_cast (J : Edges c) (D : Config G f → ℝ) (U : Config G c) :
    pass S β J (fun V => (D V:ℂ)) U = ((pass S β J D U:ℝ):ℂ) := by
  unfold pass
  simp only [Complex.real_smul,←Complex.ofReal_mul,smul_eq_mul,integral_complex_ofReal]

theorem window_split {D W : Config G f → ℝ} {F H : Config G f → ℂ}
    (h : Good S D F) (h' : Good S W H) (J : Edges c) :
    response S β D F J - response S β W H J = response S β D (F-H) J +
      response S β W H J * response S β D (fun V => ((W V-D V:ℝ):ℂ)) J := by
  funext U
  dsimp only [Pi.sub_apply,Pi.add_apply,Pi.mul_apply,response]
  rw [pass_subtract S β h.branches J h.input h'.input U]
  change _ = _ + _ * (pass S β J (fun V => (((W-D) V):ℂ)) U / _)
  rw [pass_cast,pass_subtract S β h.branches J h'.denom h.denom U,Complex.ofReal_sub]
  have d := Complex.ofReal_ne_zero.mpr (pass_pos S β J h.branches U h.denom h.positive).ne'
  have w := Complex.ofReal_ne_zero.mpr (pass_pos S β J h.branches U h'.denom h'.positive).ne'
  field_simp [d,w]
  ring

theorem window_budget (o : Site c) (X : Support c) {R : ℝ} (hr : 0 ≤ R)
    (hR : ∀ x ∈ X, (separation x o:ℝ) ≤ R) (B : BudgetPoint)
    {D W : Config G f → ℝ} {F H : Config G f → ℂ} (h : Good S D F) (h' : Good S W H)
    {e δ M : ℝ} (he : ∀ U, ‖F U-H U‖ ≤ e*D U) (hd : ∀ U, |W U-D U| ≤ δ*D U)
    (hM : ∀ U, ‖H U‖ ≤ M*W U) :
    let J := edges X
    let K := responsePrice G (β*S.kernel.penalty) B.order J.card (B.threshold*(1+R)^B.power)
    B.Regular X (response S β D F J-response S β W H J) ∧
      B.supBounds o X (response S β D F J-response S β W H J) (K*e+2^B.order*((K*M)*(K*δ))) := by
  intro J K
  let d := fun U => ((W U-D U:ℝ):ℂ)
  have v : Good S D d := ⟨h.branches,h.denom,Complex.ofRealCLM.integrable_comp (h'.denom.sub h.denom),
    h.positive,h.gauge,fun z U => by dsimp [d]; rw [h'.gauge,h.gauge]⟩
  have n : Good S D (F-H) := ⟨h.branches,h.denom,h.input.sub h'.input,h.positive,h.gauge,
    fun z U => congrArg₂ (·-·) (h.sym z U) (h'.sym z U)⟩
  have b₀ := budget_response β o X hr hR B n he
  have b₁ := budget_response β o X hr hR B h' hM
  have b₂ := budget_response β o X hr hR B v (a:=δ) (fun U => by
    simpa only [d,Complex.norm_real,Real.norm_eq_abs] using hd U)
  have s₀ := response_regular β X B n
  have s₁ := response_regular β X B h'
  have s₂ := response_regular β X B v
  have bp := bound_mul s₁ s₂ b₁ b₂
  have sp := regular_mul s₁ s₂
  rw [window_split S β h h' J]
  let A := response S β D (F-H) J
  let P := response S β W H J * response S β D d J
  change B.Regular X (A+P) ∧ B.supBounds o X (A+P) _
  have reg : B.Regular X (A+P) :=
    ⟨fun U V z => congrArg₂ (·+·) (s₀.sites U V z) (sp.sites U V z),s₀.borel.add sp.borel,
     fun z U => congrArg₂ (·+·) (s₀.symmetry z U) (sp.symmetry z U),
     fun U hu => (s₀.smooth U hu).add (sp.smooth U hu), fun U hu A _ hl =>
       left_has A hl ((s₀.smooth U hu).add (sp.smooth U hu))⟩
  refine ⟨reg,add_nonneg b₀.1 bp.1,?_⟩
  intro U hu l hl hlD
  rw [left_add (f:=A) (g:=P) l (s₀.smooth U hu) (sp.smooth U hu) hl]
  exact (norm_add_le ..).trans (add_le_add (b₀.2 U hu l hl hlD) (bp.2 U hu l hl hlD))

end YM.Integration.FVA1Physical.Round2
