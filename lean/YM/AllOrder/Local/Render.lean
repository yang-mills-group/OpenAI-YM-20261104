import YM.AllOrder.Local.Post

/-!
# Pure Taylor graded form

All coefficient kernels into `flip` independent of β. No germ equivalence
at r shrinking with trunc k: on any scaled `x` this is exact finite sum for
the same typed service (same path data ρ, β-band). Later strip with affine &
geo cover in true path recursion. No one calls this yet for outputs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Local.Pure
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented PhysicalNext Repeat Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Sienna Token Shellac Vote Work.G05
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius

section t
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f:E→ℝ) (x:E) (k : ℕ) (β:ℝ)
def chip (i:ℕ) := Tensor.diagonal (Tensor.coeff f i 0)
lemma bill_insert : blockTaylor k f (β • x) = ∑ i∈Finset.range (k+1), β^i*chip f i x := by
  unfold blockTaylor; rw [Finset.sum_apply]; exact Finset.sum_congr rfl fun i _=> Tensor.homogeneous (Tensor.coeff f i 0) x β
lemma shift_two {t:ℝ} (ht:t^2* β=1) (hx:f 0=0) (hp : fderiv ℝ f 0=0) : β*blockTaylor (k+2) f (t • x)= ∑ i∈Finset.range (k+1),t^i*chip f (i+2) x:= by
  rw [bill_insert,sum_range_succ',sum_range_succ',mul_add,mul_add]
  simp_rw [show chip f 0 x=0 from hx ▸ Tensor.coeff_apply_zero ..]
  have h1 : chip f 1 x=0:= by unfold chip Tensor.diagonal Tensor.coeff; rw [_root_.smul_apply,iteratedFDeriv_one_apply,hp]; simp
  rw [h1]; simp only [mul_zero,add_zero,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; rw [show t^(i+1+1)=t^i*t^2 from pow_add t i 2]; linear_combination t^i*chip f (i+2) x*ht
end t

section book
variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio) (T : Tube G S)
    (A : ChartRatio G) (ρ : Bid.Dir G c→AxisChart G F) (β : ℝ) (l : S.Choices) {σ C Λ : ℝ} {j n k : ℕ}
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "μ" => Lapis.orbit F ρ
local notation "f₁" => Lapis.table F l T.up T.high
local notation "ψ" => mist F A T.up
local notation "K" => Lapis.gram F T.up T.high ρ l
local notation "G₀" => gStep β
local notation "Ω" => solar F A β
local notation "Φ" => hard F T ρ l
local notation "Ψ" => soft F T A ρ l
local notation "R" => aggregation f₁ ψ μ K

def flip (j:ℕ) (x : Xs) := -chip Φ (j+2) x-chip Ψ j x + chip (Real.log ∘ R j) j (1,x)
def basis : ℝ:= Real.log Ω - Lantern.shade K 0

variable (Z : Push.Uniform.Before G σ C S.patch.J S.kernel (n+3))
    (hg : Larger (G:=G) S) (hp : T.up.Bounds T.high σ C Λ) (hr : Z.Service F T.high T.up ρ)
include Z hg hp hr
lemma hard_has : Φ 0=0 ∧ fderiv ℝ Φ 0=0 := by
  let U:=T.up; let p:=T.high; let A:= Uniform.priced F l p U
  let V:= combineH (G:=G) F; let K':= paint F G
  let f:=Function.uncurry (tested F l p U)
  let z (x:Xs):= (x,μ x)
  have ha := price_identity F l hp hg.1; have h': A=f ∘ K':= rfl
  have ht: HasFDerivAt (𝕜:=ℝ) A 0 0:= by
    rw [h']; let w:=fderiv ℝ f; have he': HasFDerivAt (𝕜:=ℝ) f 0 (K' 0):= by rw [_root_.map_zero]; exact ha.2.2.1 ▸ ((ha.1.differentiableAt (by simp)).hasFDerivAt)
    simpa only [ContinuousLinearMap.zero_comp] using he'.comp 0 (K'.hasFDerivAt)
  have hx: z 0=0:=by unfold z; rw [zeroO F T.up T.high ρ σ C Z hr]; rfl
  have hv : ContDiffAt ℝ ω z 0:= contDiffAt_id.prodMk (((weld (Precision.Key F G)).symm.contDiff.contDiffAt).comp 0 (hr.series (mem_ball_self hr.x_pos)))
  have hv': HasFDerivAt (𝕜:=ℝ) Φ 0 0:= by
    have hz : HasFDerivAt (𝕜:=ℝ) A 0 (V (z 0)):= by rw [hx,_root_.map_zero]; exact ht
    have hw:= hz.comp 0 (V.hasFDerivAt.comp 0 (hv.differentiableAt (by simp)).hasFDerivAt)
    rw [ContinuousLinearMap.zero_comp] at hw; exact hw
  rw [show (hard F T ρ l)=A ∘ V ∘ z from rfl]
  refine ⟨?_,hv'.fderiv⟩; change A (V (z 0))=_; rw [hx,_root_.map_zero]; exact ha.2.1 -- args later

omit Z hg hp hr in
lemma connect_chip (h : k ≤ j) : chip (Real.log ∘ R k) k = chip (Real.log ∘ R j) k := by
  have he i : ContDiffAt ℝ (↑(i:ℕ)) (Real.log ∘ R i) 0 := (Real.contDiffAt_log.mpr (show R i 0≠0 from ne_of_eq_of_ne collect0 one_ne_zero)).comp _ ((terms_art _).contDiffAt.of_le le_top)
  have ht: iteratedFDeriv ℝ k (Real.log ∘ R k) 0=iteratedFDeriv ℝ k (Real.log ∘ R j) 0 := by rw [←blockTaylor_jets (he k) k le_rfl, ←blockTaylor_jets (he j) k h]; exact agree h le_rfl
  unfold chip Tensor.coeff; rw [ht]

lemma bookroom (x:Xs) (he:0<β) : script F T A ρ β l k (G₀ • x)= basis F T A ρ β l + ∑ i∈ Finset.range (k+1), G₀^i*flip F T A ρ l i x:= by
  unfold script connected; let g:=G₀
  have hQ := hard_has F T ρ l Z hg hp hr
  rw [shift_two Φ x k _ (Fare.gS _ he).2 hQ.1 hQ.2,bill_insert, show (G₀,G₀ • x)=g • (1,x) by simp only [Prod.smul_mk,smul_eq_mul,mul_one,g],bill_insert]
  apply eq_add_of_sub_eq'; unfold basis; abel_nf; simp_rw [neg_one_smul,← Finset.sum_neg_distrib,← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i hi=>?_ ; unfold flip; rw [connect_chip F T A ρ l (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]; unfold g; ring
end book
end YM.AllOrder.Local.Pure
