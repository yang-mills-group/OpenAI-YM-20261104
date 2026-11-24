import YM.AllOrder.Local.Glass
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Shellac.Sables

/-!
# Independent Taylor approximation to full pure Wilson push on seam periods

Homogeneous in gStep: take field `x=b*A` (real block links), retain Taylor
terms of weight ≤ k, independent of x,A size after approximation. Classical
orders ≤ k+2. Leave Haar/prefactor normalization `Ω` untouched (known
explicitly from the local group chart). Forest axial section. No derivative
through the hard fine mask or perturbative substitution for it. This bound on
*full pushed log* survives higher jet requests.

THIS IS a pure (Pane.virgin) local step lemma, not an arbitrary activity push.
It uses `T.up` with its classical & determinant histories, handles actual
t=βhat_coarse and gStep β physical fine coupling in its scheduled band. Later
work to read that local representative/masked norm on actual data. Does not
claim universal constants at earlier choices (post-L, fixed order).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Local.Pure
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented PhysicalNext Repeat Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Sienna Token Shellac Vote Work.G05
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius

lemma freeze {X:Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {j:ℕ} {Z r t : ℝ}
    (h':ℝ×X→ℝ) (x:X) (H : Brush j Z r h' (t,x)) : Brush j Z r (h'∘ arc t) x := by
    let P:= hook X; have hx' y: arc t y=(t,0)+ P y:= by simp [P]
    rw [show h' ∘ arc t=(fun i=> h' ((t,0)+P i)) from funext fun i=>congr_arg _ (hx' i)]; exact skim _ ((hx' x) ▸ H) n_hook

section book
variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio) (T : Tube G S)
    (A : ChartRatio G) (ρ : Bid.Dir G c→AxisChart G F) (β : ℝ) (l : S.Choices) {r C U D Z u a s c' : ℝ} {j n k : ℕ}
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "μ" => Lapis.orbit F ρ
local notation "f₁" => Lapis.table F l T.up T.high
local notation "ψ" => mist F A T.up
local notation "K" => Lapis.gram F T.up T.high ρ l
local notation "φ" => coverLog F T A l ρ β
local notation "G₀" => gStep β
local notation "Ω" => solar F A β

def hard (x:Xs) := f₁ (x,μ x)
def soft (x:Xs) := ψ (x,μ x)+ Lantern.shade (K) x-Lantern.shade K 0

/-- Book copies until weight k, **before** any masks or flag partners. Uses a
Gram shared across all auxiliary insertions (none in this theorem) and
coupling coefficients of φ and ψ on that branch. This is the polynomial at a
canonical representative after factoring out the explicit prefactor. -/
def script (k:ℕ) (x:Xs) := Real.log Ω - Lantern.shade K 0 -
    β*blockTaylor (k+2) (hard F T ρ l) x - blockTaylor k (soft F T A ρ l) x +
    connected f₁ ψ μ K k (G₀,x)
def price (j:ℕ) (C:ℝ) := clump j (1+C+(1+C)) C

variable (h : Golf (Lapis.table F l T.up T.high) (mist F A T.up) (Lapis.orbit F ρ) (Lapis.gram F T.up T.high ρ l) n D U U C)
include h
lemma modest (hj : j ≤ n) {x:Xs} (hx : ‖x‖ < U) : Brush j (price j C) 1 (hard F T ρ l) x ∧ Brush j (price j C+C) 1 (soft F T A ρ l) x := by
  -- split version of Token.promise
  let f y:=(y,μ y)
  have hh:= h.curve x hx; have hC:= hh.nonneg; let I:= ContinuousLinearMap.id ℝ Xs
  have hp: Brush j (1+ C) 1 I x := by
    refine ((Brush.linearB I (u:=1) ?_ ?_ zero_le_one).climb (le_add_of_nonneg_right hC) le_rfl)
    · exact hx.le.trans h.small
    simp [I,ContinuousLinearMap.norm_id_le]
  have hv : Brush j (1+C+(1+C)) 1 f x:= hp.pair ((hh.smaller (by omega)).climb (le_add_of_nonneg_left zero_le_one) le_rfl)
  obtain ⟨h₁,h₂⟩:= h.color 0 0 (0,x) (show ‖(0:Poll.Body (Precision.Key F G))‖≤D by rw [norm_zero]; exact h.off) (by simp) (show ‖(0:ℝ)‖<U by rw [norm_zero]; exact h.pos) hx
  rw [show Lantern.visit μ 0 0 (0,x)=f x from (by simp [Lantern.visit,f])] at h₁ h₂; refine ⟨(composite hv (h₁.smaller (by omega))), ((composite hv (h₂.smaller hj)).gathering ((h.gram x hx).2.smaller hj)).shimmy ?_⟩; refine Eventually.of_forall fun i=>?_ ; unfold soft; change ψ (f i) +_ -_=ψ (f i)+_; abel

lemma poem (B : BudgetPoint) (hj : k+3 ≤ j) (hp : j ≤ n) (he : 0<β)
    {x:Xs} (hx : ‖(G₀,x)‖ ≤ r) (hr : r < U) (hh : Brush j a 1 (lack F T A B ρ β l D) x)
    (H : Brush j Z (r⁻¹) (cleanLog f₁ ψ μ K D-connected f₁ ψ μ K k) (G₀,x)) :
    Brush j (a+ β*(price j C*r^(k+3))+(price j C+C)*r^(k+1)+Z) (r⁻¹) (pures T B β-script F T A ρ β l k) x := by
  let W:=lack F T A B ρ β l D
  let f:= hard F T ρ l; let g:= soft F T A ρ l; let h' : ℝ×Xs→ℝ:= cleanLog f₁ ψ μ K D-connected f₁ ψ μ K k
  have hδ:= (Fare.gS _ he).1
  have ht : ‖x‖ ≤ r := (norm_snd_le _).trans hx; have hv := hr.le.trans h.small
  have hr' : 0<r:= lt_of_lt_of_le hδ (show G₀ ≤ r from le_trans (le_abs_self _) ((norm_fst_le _).trans hx)); have hb y (he:‖(y:Xs)‖ ≤ r) := modest F T A ρ l h hp (he.trans_lt hr)
  have hA := (Taylor.forecast hr' hv hj (fun i hi=> (hb i hi).1) ht).smul β
  have hzB := Taylor.forecast (f:=g) (j:=k) hr' hv (show k+1≤j by omega) (fun i hi=> (hb i hi).2) ht
  rw [Real.norm_of_nonneg he.le] at hA
  have hg : Brush j Z (r⁻¹) (h' ∘ arc G₀) x:= by
    exact freeze (X:=Xs) (t:=G₀) h' x H
  refine ((((hh.climb le_rfl ((one_le_inv₀ hr').2 hv)).separating hA).separating hzB).gathering hg).shimmy ?_
  refine Eventually.of_forall fun i=>?_; change pures T B β i-script F T A ρ β l k i=((pures T B β i - Real.log Ω+ φ i-cleanLog f₁ ψ μ K D (G₀,i))- β * (f i-blockTaylor (k+2) f i)-(g i-blockTaylor k g i))+(cleanLog f₁ ψ μ K D (G₀,i)-connected f₁ ψ μ K k (G₀,i)); unfold script g soft coverLog f hard; ring -- notation phi unfold parse
end book
end YM.AllOrder.Local.Pure
