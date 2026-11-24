import YM.Integration.WilsonOriginalPublicPlantedPivotFields
import YM.Integration.WilsonOriginalPublicPlantedGram
import YM.Integration.WilsonOriginalPublicPivotCross

/-! The genuine finite Wilson product on the two dressed pivot fields is
coercive on the protected reflected region. The finite center weights may
be signed and may share all cutoff parameters with the fields. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalPublicPlantedGramFilms
open Set Finset Filter Function Metric Lattice Maxwell Maxwell.Wick XSpace XSpace.Cirrus
open XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Register MS MS.Land MS.Menus MS.Theater
open Source Labels Local.Physical PowerSeries
open WilsonPositionProgramPublicReflectedRead WilsonPositionProgramPublicWickGram
open WilsonOriginalPublicPlantedPivotFields WilsonOriginalPublicPivotCross
open WilsonOriginalPublicPlantedGram (measured)
open scoped Topology Classical BigOperators
variable {G:Gauge}(Z:WilsonPrescription G){g:G.Simple}
    {M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{T:Prescription (Press.portDeck G)}
    {dial:Bool}(H:Main.Match Z g M T dial){d:ℕ}{I:Type}[Fintype I]{β:Local.Physical.Deck G}
    (a:Axis)(leg:I→Glyph β d){L:Type}[Fintype L]

def reflected (j:ℕ)(v:Glyph β d):Film Z.scheme:=fun s=>
  plant Z.scheme β (WilsonPositionRawEpoch.matrix Z j d) s 0
    (τ (Signed.mirror a) d (Theater.Daylight β d v))

def pupil (j:ℕ)(v:Glyph β d):Film Z.scheme:=fun s=>
  plant Z.scheme β (WilsonPositionRawEpoch.matrix Z j d) s 1 (Theater.Daylight β d v)

omit [Fintype I] in
theorem sampled {j B:ℕ}(P:Handoff.Directory Z j B)(X:L→Sample 2)(μ:L→ℂ)
    (hs:∀l,(X l).F=Z.run.step j)(q:ℕ)(cap:Handoff.Directory.budget G 2 d+q≤B)(u:ℝ)(i k:I):
    detector Z.scheme X μ q u (reflected Z a j (leg i)*pupil Z j (leg k)) =
      ∑l,μ l*measured Z a leg q P u (X l) i k := by
  simp only [detector,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,
    LinearMap.proj_apply,Pi.mul_apply,smul_eq_mul]
  apply sum_congr rfl
  intro l _
  rw [measured,drawn β Z P (X l) (signed a leg i k) (hs l) q cap u]
  apply congrArg (μ l * ·)
  rw [show Finset.Iic q=Finset.range (q+1) by ext t;simp]
  apply sum_congr rfl
  intro m _
  rw [Fin.prod_univ_two,mul_comm]
  rfl

private theorem combine (A:L→I→I→ℂ)(G₀:I→I→ℂ)(μ:L→ℂ)(C ε:ℝ)
    (mass:∑l,μ l=1)(tv:∑l,‖μ l‖≤C)(he:0≤ε)(fee:∀l,‖A l-G₀‖≤ε) :
    ‖(fun i k=>∑l,μ l*A l i k)-G₀‖≤C*ε := by
  have hc:0≤C:=le_trans (sum_nonneg fun _ _=>norm_nonneg _) tv
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hc he)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hc he)).mpr
  intro k
  change ‖(∑l,μ l*A l i k)-G₀ i k‖≤C*ε
  rw [show (∑l,μ l*A l i k)-G₀ i k=∑l,μ l*(A l i k-G₀ i k) by
    simp only [mul_sub,sum_sub_distrib,←sum_mul,mass,one_mul]]
  calc
    _≤∑l,‖μ l*(A l i k-G₀ i k)‖:=norm_sum_le ..
    _≤∑l,‖μ l‖*ε:=by
      apply sum_le_sum
      intro l _
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (norm_le_pi_norm ((A l-G₀) i) k).trans
        ((norm_le_pi_norm (A l-G₀) i).trans (fee l))
    _≤C*ε:=by rw [←sum_mul];exact mul_le_mul_of_nonneg_right tv he

include H in
theorem original (δ C:ℝ)(hd:0<δ)(hc:0<C)(l:Filter ℝ){t:ℝ→ℝ}
    (pos:∀ᶠ r in l,0<t r)(small:Tendsto t l (𝓝 0))(D:ℕ)(J:ℝ)(q:ℕ):
    ∃ j₀:ℕ,∃ ρ:ℝ,0<ρ ∧ ∀ᶠ r in l,∀j≥j₀,(j:ℝ)≤J*(-Real.log (t r))^D →
      ∀{B}(_P:Handoff.Directory Z j B),Handoff.Directory.budget G 2 d+q≤B →
      ∀(X:L→Sample 2)(μ:L→ℂ),(∀h,(X h).F=Z.run.step j) →
      (∀h,welcome (X h) ∧ dist (familiar (X h)) (lower a)<ρ) →
      ∑h,μ h=1 → ∑h,‖μ h‖≤C → ∀u:ℝ,|u|≤8*t r →
      ‖(fun i k=>detector Z.scheme X μ q u (reflected Z a j (leg i)*pupil Z j (leg k)))-
        reading a (nodes a) leg‖≤δ := by
  obtain ⟨j₀,ρ,hr,paid⟩:=WilsonOriginalPublicPlantedGram.original Z H a leg q (δ/C)
    (div_pos hd hc) l pos small D J
  refine ⟨j₀,ρ,hr,?_⟩
  filter_upwards [paid] with r sal j ge short B P cap X μ hs admissible mass tv u hu
  simp_rw [sampled Z a leg P X μ hs q cap u]
  have fee(h:L):=sal j ge short P cap (X h) (hs h) (admissible h).1 (admissible h).2 u hu
  exact (combine _ _ μ C (δ/C) mass tv (div_pos hd hc).le fee).trans_eq (mul_div_cancel₀ δ hc.ne')

end YM.Integration.WilsonOriginalPublicPlantedGramFilms
