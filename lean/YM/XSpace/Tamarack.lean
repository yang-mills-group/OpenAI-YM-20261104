import YM.XSpace.Salve
/-!
# First coupling-measured reports

 Defined all-orders formal series, still on the inversion regulator. Their perturbative indirection fully removed through order1 (shares Front). This is the position-normalized `G^X`, before N generic in all orders. No asympt series limits other than stated.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Rose
open Function Set Filter PowerSeries Cirrus Photo Normalize Structure1 Retirement Maxwell Graph3 MeasureTheory
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}(W:Initialize G) {V:Store G}(Y:Rose.Pick V)(l:Mesh){n e:ℕ}(d:ℕ)(g:G.Simple)
local notation "z"=> χ W Y l
abbrev α (e k:ℕ):ℝ:= (coeff e (z^k)).re
lemma αcanonical (e k:ℕ): (↑(α W Y l e k):ℂ)= coeff e (z^k):=by
  set q:= coeff e (z^k); have h : ℛ q=q:=by unfold q; rw [← coeff_map, map_pow,realχ]
  apply Complex.ext; rfl; change 0=q.im; have ht : -q.im=q.im:= congr_arg Complex.im h; linarith
variable {E:Type*}[AddCommMonoid E][Module ℝ E]
def turn {A:Type*}[AddCommMonoid A][Module ℝ A](v:ℕ→A)(e:ℕ): A:= ∑ k∈Finset.range (e+1),α W Y l e k • v k
@[simp] lemma turn_rest (v:ℕ→ E): turn W Y l v 0=v 0:=by simp [turn,α]
abbrev coef := (coeff 1 z).re
lemma turn_one (v:ℕ→ E): turn W Y l v 1 = coef W Y l • v 1:=by rw [turn,Finset.sum_range_succ]; simp [α, coef]
lemma turn_coins (v:ℕ→ℂ)(e:ℕ): turn W Y l v e= coeff e ((PowerSeries.mk v).subst z):=by
  simp_rw [turn,FPS.coeff_substituted _ (χzero W Y l),Complex.real_smul,αcanonical, coeff_mk, smul_eq_mul]; exact Finset.sum_congr rfl fun i _=> mul_comm ..
-- Horizon reports and their point kernels. Ordinary correlation & first two orders converging.
def proposed (d:ℕ): Reports G d:= turn W Y l (V.opens W l d)
def measureₓ (d:ℕ)(x: Sample n)(e:ℕ): Point G d n:= turn W Y x.F (cooked W V d x) e
lemma measure_paid (x: Sample n)(p:Tags G d n) (e:ℕ): measureₓ W Y d x e p= turn W Y x.F (fun i=> cooked W V d x i p) e:=by simp only [measureₓ,turn,_root_.sum_apply,_root_.smul_apply]
lemma sent (t:Test n)(p:Tags G d n)(e:ℕ): proposed W Y l d e n t p= turn W Y l (fun i=> V.opens W l d i n t p) e:=by simp only [proposed,turn,Finset.sum_apply,LinearMap.sum_apply,sum_apply,Pi.smul_apply,LinearMap.smul_apply,smul_apply] -- instance transparency
lemma represents (t:Test n)(p: Tags G d n): proposed W Y l d e n t p= Deposit l (fun i=> measureₓ W Y d i e p) t:=by
  rw [sent]; simp_rw [← smeared W V d p, measure_paid]; unfold turn Deposit; dsimp only; simp_rw [Complex.real_smul,Finset.mul_sum,← mul_assoc]; rw [Finset.sum_comm (s:=Finset.range (e+1))]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; ring
variable (p:Tags G d n)
include g in
lemma conjures1 : Senses (conf n) (fun i=> measureₓ W Y d i 1 p) (fun x=>checked1 W V d x p):= by
  intro x hx; simp_rw [measure_paid,turn_one]; let L:=Gate x; have hh:Tendsto (fun i:Sample n=> coef W Y i.F) L (𝓝 1):= (Complex.continuous_re.continuousAt.tendsto.comp (χlimit W Y g)).comp (liftG x); simpa only [one_smul] using hh.smul (scans1 W V d p x hx)
lemma conjures0 : Senses (conf n) (fun i=> measureₓ W Y d i 0 p) (fun x=> scene x d p):= by simp_rw [measure_paid,turn_rest]; exact scans0 W V d p
include g in
theorem follows₁ (t: Test n): Tendsto (fun l=> proposed W Y l d 1 n t p) Front (𝓝 (kernel1 W V d n t p)):= by
  simp_rw [represents W Y]; exact sees_test (conf n) t _ (conf_open n) (conjures1 W Y d g p) (fun _ _ _=>rfl) t.tsupport_subset
lemma follows₀ (t:Test n): Tendsto (fun l=> proposed W Y l d 0 n t p) Front (𝓝 (reference G d n t p)):=by
  simp_rw [represents W Y]; exact sees_test (conf n) t _ (conf_open n) (conjures0 W Y d p) (fun _ _ _=> rfl) t.tsupport_subset
include g in
theorem paying₁ (K:Set (Points n))(H:IsCompact K)(h: K⊆conf n)(e:ℝ)(he:0<e): ∀ᶠ l in Front,∀ t : Test n,tsupport t⊆K →∀ c:ℝ,TestBudget.Bound t c → ‖proposed W Y l d 1 n t p - kernel1 W V d n t p‖ ≤ c*e := by
  simp_rw [represents W Y]; exact graduate (V:=conf n) _ (fun x=> checked1 W V d x p) (conf_open _) (continuously W V d p) h H (conjures1 W Y d g p) (fun _ _ _=>rfl) e he
end YM.XSpace.Rose
