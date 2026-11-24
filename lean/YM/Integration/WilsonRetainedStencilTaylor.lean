import YM.Integration.WilsonCoherentFrozenTaylor
import YM.Integration.WilsonCoherentReportingFrame
import YM.Dict06.Wilson.Section

/-! Global real Taylor error of a bounded, compact Wilson stencil.
The finite direction space contains only the submitted intrinsic links. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRetainedStencilTaylor
open Set Finset Filter Function Lattice Wilson Source Labels Dict06.Series Dict06.Wil
open PhysicalNext.Repeat.Legato
open scoped BigOperators Classical ContDiff Topology Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

private theorem remainder {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f:E→ℂ) (sm:ContDiff ℝ ω f) (B:ℝ) (bound:∀x,‖f x‖≤B) (p:ℕ) :
    ∃ C:ℝ, 0≤C ∧ ∀ a:E, ∀ t:ℝ, 0<t →
      ‖f (t•a) - ∑ j∈range (p+1),t^j • ordinary j (fun u:ℝ=>f (u•a))‖ ≤ C*(t*‖a‖)^(p+1) := by
  obtain ⟨c,hc,localPrice⟩:=WilsonCoherentFrozenTaylor.purchased f sm (fun _:Unit=>(0:E)) continuous_const p
  let fee (j:ℕ):=‖iteratedFDeriv ℝ j f 0‖
  let bank:=∑ j∈range (p+1), fee j
  have hB:0≤B:=(norm_nonneg _).trans (bound 0)
  have hb:0≤bank:=sum_nonneg fun _ _=>norm_nonneg _
  refine ⟨max c (B+bank),hc.trans (le_max_left ..),?_⟩
  intro a t ht
  by_cases small:t*‖a‖<1
  · have paid:=localPrice () a t ht small
    simp only [zero_add] at paid
    exact paid.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity))
  have large:1≤t*‖a‖:=le_of_not_gt small
  let h:=(t*‖a‖)^(p+1)
  have hh:1≤h:=one_le_pow₀ large
  have row (j:ℕ)(hj:j∈range (p+1)) :
      ‖t^j • ordinary j (fun u:ℝ=>f (u•a))‖ ≤ fee j*h:=by
    have pos:0≤(j.factorial:ℝ)⁻¹:=by positivity
    have unit:(j.factorial:ℝ)⁻¹≤1:=inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos j)
    have cap:= (iteratedFDeriv ℝ j f 0).le_opNorm (fun _=>a)
    simp only [prod_const,card_univ,Fintype.card_fin] at cap
    unfold ordinary
    rw [Next.Foundations.iteratedDeriv_on_line (sm.contDiffAt.of_le le_top),norm_smul,norm_smul,
      Real.norm_of_nonneg (pow_nonneg ht.le _),Real.norm_of_nonneg pos]
    calc
      _ ≤ t^j * (fee j * ‖a‖^j) := mul_le_mul_of_nonneg_left
        ((mul_le_of_le_one_left (norm_nonneg _) unit).trans cap) (pow_nonneg ht.le _)
      _ = fee j * (t*‖a‖)^j := by rw [mul_pow];ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ large (Nat.le_of_lt (mem_range.mp hj))) (norm_nonneg _)
  have sumCost : ‖∑ j∈range (p+1), t^j • ordinary j (fun u:ℝ=>f (u•a))‖≤bank*h:=
    (norm_sum_le _ _).trans ((sum_le_sum row).trans_eq (Finset.sum_mul ..).symm)
  calc
    _ ≤ B + bank*h := (norm_sub_le ..).trans (add_le_add (bound _) sumCost)
    _ ≤ B*h + bank*h := add_le_add (le_mul_of_one_le_right hB hh) le_rfl
    _ = (B+bank)*h := (add_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) (zero_le_one.trans hh)

variable {G:Gauge} (R:Run G) {I:Type} [Fintype I] (d:I→ℕ)

abbrev Fragment := ∀ i:I, Panel (R.family.localSection (d i)).stencil G

def material (y:∀i,R.family.label (d i)) (x:Fragment R d) : ℂ :=
  ∏ i,echo (R.family.localSection (d i)) (y i) (x i)

theorem smooth (y:∀i,R.family.label (d i)) : ContDiff ℝ ω (material R d y) := by
  have all (s:Finset I) : ContDiff ℝ ω (fun x:Fragment R d =>
      ∏ i∈s,echo (R.family.localSection (d i)) (y i) (x i)) := by
    induction s using Finset.induction_on with
    | empty => simpa using (contDiff_const : ContDiff ℝ ω (fun _ : Fragment R d=>(1:ℂ)))
    | insert j s hj ih =>
      simp_rw [prod_insert hj]
      exact ((echo_smooth _ _).comp ((ContinuousLinearMap.proj j :
        Fragment R d →L[ℝ] Panel (R.family.localSection (d j)).stencil G).contDiff)).mul ih
  exact all univ

private theorem capped {e:ℕ} {F:Frame G e} (S:SectionData F) (y:F.Coeff) :
    ∃ B:ℝ, ∀ x:Panel S.stencil G, ‖echo S y x‖≤B:=by
  let read (u:UsedEdges S.stencil→G.El) :=
    MvPolynomial.eval (fun i:Source.Index G S.stencil=>flag i.2.1 i.2.2.1 i.2.2.2 (G.mat (u i.1))) (S.evalC y)
  have cont:Continuous read:=(MvPolynomial.continuous_eval _).comp (continuous_pi fun i=>
    (flag i.2.1 i.2.2.1 i.2.2.2).continuous.comp (G.continuous_mat.comp (continuous_apply i.1)))
  obtain ⟨B,bill⟩:=isCompact_univ.exists_bound_of_continuousOn cont.continuousOn
  exact ⟨B,fun x=>bill (fun i=>G.lieExp (x i)) (mem_univ _)⟩

theorem section_price (y:∀i,R.family.label (d i)) (p:ℕ) :
    ∃ C:ℝ, 0≤C ∧ ∀ a:Fragment R d, ∀ t:ℝ, 0<t →
      ‖material R d y (t•a) - ∑ j∈range (p+1),t^j • ordinary j (fun u:ℝ=>material R d y (u•a))‖
        ≤ C*(t*‖a‖)^(p+1) := by
  choose b bound using fun i:I=>capped (R.family.localSection (d i)) (y i)
  apply remainder (material R d y) _ (∏ i,b i) _ p
  · exact smooth R d y
  · intro x
    rw [material,norm_prod]
    exact prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>bound i (x i))

end YM.Integration.WilsonRetainedStencilTaylor
