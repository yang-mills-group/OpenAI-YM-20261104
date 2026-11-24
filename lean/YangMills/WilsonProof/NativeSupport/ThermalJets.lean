import YM.RGComparison.Core16.Plaquette
import YM.RGComparison.Core16.Offset

/-! The signed temperature Hessian and microscopic curl legs on the complete
Core16 tree slice, with the original joint precision and no ambient dimension factor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ThermalShortcuts.ThermalJets
open Lattice RG Tree Wilson Precision Push.BetaTransport RGComparison.Core16
open Function Filter MeasureTheory Set Metric Exterior Work.F03
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open PertExtension PertExtension.Series Tested Radial GaussianScore
open Descent
variable {G : Gauge} {n c : Side} {d : Descent n c}
local notation "E" => Coordinates G d

def charged (G : Gauge) (d : Descent n c) (t : d.Tags) (v : ℕ → ℝ) (x : Coordinates G d) :=
  d.account v t 1 (d.tablePath x)

def signedForm (G : Gauge) (d : Descent n c) (t : d.Tags) (v : ℕ → ℝ) :
    Coordinates G d →ₗ[ℝ] Module.Dual ℝ (Coordinates G d) where
  toFun x := (fderiv ℝ (fderiv ℝ (charged G d t v)) 0 x).toLinearMap
  map_add' x y := by simp
  map_smul' r x := by simp

theorem signed_half (t : d.Tags) (v : ℕ → ℝ) (x : E) :
    jet (charged G d t v) 2 x = signedForm G d t v x x / 2 := by
  unfold jet signedForm
  rw [iteratedFDeriv_two_apply]
  dsimp; ring

theorem charged_grade (ok : d.OK G) (t : d.Tags) {v : ℕ → ℝ} {M : ℝ}
    (hb : d.Band M v) : RadialOrder 2 (charged G d t v) := by
  intro x
  obtain ⟨C,hC,h⟩ := action_grade t ok x
  refine ⟨M*C,mul_nonneg (nonnegativeBand hb) hC,?_⟩
  filter_upwards [h] with r hr
  have ha := action_nonneg (G:=G) d t (1 : Config G c) (d.tablePath (r • x))
  change ‖d.action t 1 (d.tablePath (r • x))‖ ≤ C*r^2 at hr
  rw [Real.norm_of_nonneg ha] at hr
  exact (total_charge t hb _ _).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hr (nonnegativeBand hb))

theorem signed_le_precision (ok : d.OK G) (t : d.Tags) {v : ℕ → ℝ} {M : ℝ}
    (hb : d.Band M v) (x : E) :
    |signedForm G d t v x x| ≤ M * quadratic G d t x x := by
  have hs : ContDiffAt ℝ ∞ (charged G d t v) 0 := (account_smooth ok t v).of_le le_top
  have H := directions (f:=charged G d t v) hs x
  have L := (H.shift (w:=2) (fun i hi => H.vanish (charged_grade ok t hb x) hi)).tendsto_first
  have bound : |jet (charged G d t v) 2 x| ≤ M * jet (d.phase G t) 2 x := by
    apply le_of_tendsto_of_tendsto L.abs ((apices ok t x).const_mul M)
    apply Eventually.of_forall
    intro r
    change |r⁻¹^2 * charged G d t v (r • x)| ≤ M * (r⁻¹^2 * d.phase G t (r • x))
    rw [abs_mul, abs_of_nonneg (sq_nonneg _),mul_left_comm M]
    exact mul_le_mul_of_nonneg_left (total_charge t hb 1 (d.tablePath (r • x))) (sq_nonneg _)
  rw [signed_half,half,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] at bound
  linarith

theorem face_le_action (d : Descent n c) (t : d.Tags) (f : Face (Per n)) (V : Config G c)
    (x : Descent.Fields G d) : face G f (d.fine V x) ≤ d.action t V x := by
  induction d with
  | nil =>
    change G.price (faceValue V f) ≤ 1 * ∑ i, G.price (faceValue V i)
    rw [one_mul]
    exact Finset.single_le_sum (fun i _ => (G.price_range (faceValue V i)).1) (Finset.mem_univ f)
  | @push m i S T d ih =>
    rw [action_push]
    exact (ih t.2 _ _).trans (le_add_of_nonneg_left ((energy_estimate S _).nonneg V))

theorem curl_le_precision (ok : d.OK G) (t : d.Tags) (f : Face (Per n)) (x : E) :
    ‖faceCurl f (topDir d x)‖^2 ≤ quadratic G d t x x := by
  let A := face G f ∘ d.fine 1 ∘ d.tablePath
  have H := directions (f:=A) (face_test d f).smooth x
  have L := (H.shift (w:=2) (fun i hi => H.vanish (graded_face d f x) hi)).tendsto_first
  have h : jet A 2 x ≤ jet (d.phase G t) 2 x := by
    apply le_of_tendsto_of_tendsto L (apices ok t x)
    exact Eventually.of_forall fun r =>
      mul_le_mul_of_nonneg_left (face_le_action d t f 1 (d.tablePath (r • x))) (sq_nonneg _)
  rw [show jet A 2 x = _ from face_jet d f x,half] at h
  linarith

/-- The transported curvature's leading coordinate at the actual microscopic face. -/
def leg (G : Gauge) (d : Descent n c) (f : Face (Per n)) (i : G.ColorIndex) :
    Module.Dual ℝ (Coordinates G d) where
  toFun x := (faceCurl f (topDir d x)) i
  map_add' x y := by simp [faceCurl,dColor,parts,Matrix.mulVec,dotProduct, mul_add,Finset.sum_add_distrib]
  map_smul' r x := by
    simp [faceCurl,dColor,parts,Matrix.mulVec,dotProduct,Finset.mul_sum, mul_left_comm]

theorem leg_le_precision (ok : d.OK G) (t : d.Tags) (f : Face (Per n)) (i : G.ColorIndex) (x : E) :
    (leg G d f i x)^2 ≤ quadratic G d t x x := by
  have h := PiLp.norm_apply_le (faceCurl f (topDir d x)) i
  have h' := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [Real.norm_eq_abs,sq_abs] at h'
  exact h'.trans (curl_le_precision ok t f x)

section Sandwich
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
local notation "V" => Module.Dual ℝ X
variable (Γ : Law X)

def UnitLeg (ℓ : V) := ∀ x, (ℓ x)^2 ≤ Γ.P x x

theorem inverse_energy {ℓ : V} (h : UnitLeg Γ ℓ) : Γ.P (Γ.inverse ℓ) (Γ.inverse ℓ) ≤ 1 := by
  have p := h (Γ.inverse ℓ)
  rw [Γ.applies] at p ⊢
  nlinarith [sq_nonneg (ℓ (Γ.inverse ℓ)-1)]

theorem wick_le_one {a b : V} (ha : UnitLeg Γ a) (hb : UnitLeg Γ b) :
    |Γ.wick a b| ≤ 1 := by
  have p := (hb (Γ.inverse a)).trans (inverse_energy Γ ha)
  change |b (Γ.inverse a)| ≤ 1
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (b (Γ.inverse a)+1),sq_nonneg (b (Γ.inverse a)-1)]

theorem sandwich {D : X →ₗ[ℝ] V} {M : ℝ} (hM : 0 ≤ M)
    (sym : ∀ x y,D x y = D y x) (dom : ∀ x, |D x x| ≤ M*Γ.P x x)
    {a b : V} (ha : UnitLeg Γ a) (hb : UnitLeg Γ b) :
    |D (Γ.inverse a) (Γ.inverse b)| ≤ M := by
  let x := Γ.inverse a
  let y := Γ.inverse b
  have px : Γ.P x x ≤ 1 := inverse_energy Γ ha
  have py : Γ.P y y ≤ 1 := inverse_energy Γ hb
  have pair : Γ.P (x+y) (x+y)+Γ.P (x-y) (x-y)=2*(Γ.P x x+Γ.P y y) := by
    simp only [map_add,map_sub,LinearMap.add_apply,LinearMap.sub_apply]; ring
  have pol : D (x+y) (x+y)-D (x-y) (x-y)=4*D x y := by
    simp only [map_add,map_sub,LinearMap.add_apply,LinearMap.sub_apply,sym y x]; ring
  have v := (abs_sub (D (x+y) (x+y)) (D (x-y) (x-y))).trans (add_le_add (dom (x+y)) (dom (x-y)))
  rw [pol,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4),← mul_add,pair] at v
  change |D x y| ≤ M
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add px py) hM]

end Sandwich

/-- Each two-source attachment of the entire signed temperature Hessian,
already summed over all layers/sites and with the original inverse precision. -/
theorem joined (room : d.Room G) (t : d.Tags) {v : ℕ → ℝ} {M : ℝ} (hb : d.Band M v)
    (f₁ f₂ : Face (Per n)) (i₁ i₂ : G.ColorIndex) :
    |signedForm G d t v ((ambient t room).inverse (leg G d f₁ i₁))
      ((ambient t room).inverse (leg G d f₂ i₂))| ≤ M :=
  sandwich (ambient t room) (nonnegativeBand hb)
    (fun _ _ => (account_smooth (room_ok d room) t v).isSymmSndFDerivAt_of_omega.eq ..)
    (signed_le_precision (room_ok d room) t hb)
    (leg_le_precision (room_ok d room) t f₁ i₁) (leg_le_precision (room_ok d room) t f₂ i₂)

end YM.Integration.ThermalShortcuts.ThermalJets
