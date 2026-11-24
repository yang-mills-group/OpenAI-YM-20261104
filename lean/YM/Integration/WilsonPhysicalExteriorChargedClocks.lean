import YM.Integration.WilsonPhysicalExteriorIndependentPrice
import YM.Integration.WilsonPhysicalExteriorCompactWindow

/-! Independent subtraction arguments at the two preselected original
Wilson stops; the estimate is uniform in every choice of far or near leg. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorChargedClocks
open Filter Real Finset RG RG16 PhysicalNext.Repeat.Legato
open WilsonPhysicalExteriorMeshStops WilsonPhysicalExteriorActualSides
open WilsonPhysicalExteriorIndependentPrice
open scoped Topology Classical
variable {G:Gauge} (R:Run G)
local notation "Λ₀" => RG16.Lambda R.family.path.levels
local notation "s₀" => R.family.S.scale

def argument (c c' μ:ℝ) (original exterior:Bool) (j:ℕ) : ℝ :=
  (if original then μ+s₀ j else μ)-WilsonPhysicalExteriorActualSides.time R c j+
    (if exterior then s₀ j-s₀ (WilsonPhysicalExteriorMeshStops.far R.family c' j) else 0)

private theorem term (hG:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤log (Λ₀ m))
    {c c':ℝ} (low:1≤c) (middle:c'≤c) (high:c≤2) (μ:ℝ) :
    ∀ᶠ j:ℕ in atTop,∀ u f:Bool,|argument R c c' μ u f j|≤5*exp (2*Λ₀ j) := by
  have rise:=tendsto_exp_atTop.comp (Literal.lambda_leads R.family hG)
  filter_upwards [WilsonPhysicalExteriorFirstCutScale.shift R hG μ,
    time_at_most R hG slow low,far_window R.family hG slow c',rise.eventually_ge_atTop |μ|] with j hs hθ hF hr
  have hΛ:1≤Λ₀ j:=by linarith only [Literal.lambda_up R.family j]
  have hb:0≤Λ₀ j:=zero_le_one.trans hΛ
  have hE:exp (Λ₀ j)≤exp (2*Λ₀ j):=exp_le_exp.mpr (by linarith)
  have sq:(Λ₀ j)^c≤exp (2*Λ₀ j):=by
    have h:=rpow_le_rpow_of_exponent_le hΛ high
    rw [Real.rpow_two] at h
    calc
      _≤(Λ₀ j)^2:=h
      _≤(exp (Λ₀ j))^2:=pow_le_pow_left₀ hb (by linarith only [add_one_le_exp (Λ₀ j)]) _
      _=_:=by rw [two_mul,exp_add,pow_two]
  have near:0≤WilsonPhysicalExteriorActualSides.time R c j:=(rpow_nonneg hb c).trans (time_at_least R c j)
  have far0 : 0 ≤ s₀ j-s₀ (WilsonPhysicalExteriorMeshStops.far R.family c' j):=sub_nonneg.mpr ((OPE.scale_mono R.family.S).monotone hF.1)
  have f:(s₀ j-s₀ (WilsonPhysicalExteriorMeshStops.far R.family c' j))≤exp (2*Λ₀ j):=
    hF.2.2.trans ((rpow_le_rpow_of_exponent_le hΛ middle).trans sq)
  intro u b
  let p:=if u=true then μ+s₀ j else μ
  let a:=if b=true then s₀ j-s₀ (WilsonPhysicalExteriorMeshStops.far R.family c' j) else 0
  have hp:|p|≤exp (2*Λ₀ j):=by cases u <;> dsimp [p] <;> first | exact hr.trans hE | linarith
  have ha:|a|≤exp (2*Λ₀ j):=by
    cases b
    · simpa [a] using (exp_pos (2*Λ₀ j)).le
    · simpa [a,abs_of_nonneg far0] using f
  change |p-WilsonPhysicalExteriorActualSides.time R c j+a|≤_
  have h₁:=abs_add_le (p-WilsonPhysicalExteriorActualSides.time R c j) a
  have h₂:=abs_sub p (WilsonPhysicalExteriorActualSides.time R c j)
  rw [abs_of_nonneg near] at h₂
  linarith

/-- A single original entrance for an entire finite list of prechosen
subtraction points and every selection of their physical or rescaled logs. -/
theorem all {W:Type} [Fintype W] (hG:G.Simple)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤log (Λ₀ m))
    {c c':ℝ} (low:1≤c) (middle:c'≤c) (high:c≤2) (μ:W×Fin 3→ℝ) :
    ∀ᶠ j:ℕ in atTop,∀ u f:W×Fin 3→Bool,
      length (fun i=>argument R c c' (μ i) (u i) (f i) j)≤exp (3*Λ₀ j) := by
  let I:=W×Fin 3
  have ht:∀ᶠ j:ℕ in atTop,∀i:I,∀u f:Bool,|argument R c c' (μ i) u f j|≤5*exp (2*Λ₀ j) :=
    Filter.eventually_all.mpr (fun i=>term R hG slow low middle high (μ i))
  have grow:=tendsto_exp_atTop.comp (Literal.lambda_leads R.family hG)
  filter_upwards [ht,grow.eventually_ge_atTop (1+5*(Fintype.card I:ℝ))] with j hj hcard u f
  have h:=sum_le_sum (s:=univ) (fun i _=>hj i (u i) (f i))
  have e:1≤exp (2*Λ₀ j):=one_le_exp (by linarith only [Literal.lambda_up R.family j])
  have hh:=mul_le_mul_of_nonneg_right hcard (exp_pos (2*Λ₀ j)).le
  simp only [sum_const,card_univ,nsmul_eq_mul] at h
  unfold length
  rw [show 3*Λ₀ j=Λ₀ j+2*Λ₀ j by ring,exp_add]
  dsimp only [I,Function.comp_apply] at hh h ⊢
  nlinarith only [h,hh,e]

end YM.Integration.WilsonPhysicalExteriorChargedClocks
end
