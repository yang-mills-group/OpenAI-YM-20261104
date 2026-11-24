import YM.RGComparison.Core16.Absolute

/-!
# Perturbing real path parameters in the finite-history consumer

Accounts for costs explicitly (one possible, volume-expensive bound). `u i` here means the reset
of inverse squared coupling relative to `a⁻²`. `h` is `d.Room G` in the comparison: the two
paths of couplings DON'T have to both occur on a lawful trajectory. One will be evaluated on the
physical history.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Descent
open Lattice RG Tree Wilson Precision Push.BetaTransport
open Function Filter MeasureTheory Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open PertExtension PertExtension.Series Tested Radial
variable {G : Gauge} {n c : Side} {d : Descent n c} (h : d.OK G)
    {u v : ℕ → ℝ} {M δ a : ℝ} (t : d.Tags)

abbrev Band (d : Descent n c) (M : ℝ) (u : ℕ → ℝ) := ∀ i ≤ d.depth, ‖u i‖ ≤ M

lemma nonnegativeBand (h : d.Band M u) : 0 ≤ M := (norm_nonneg (u 0)).trans (h 0 (Nat.zero_le _))

lemma total_charge (hU : d.Band M u) (V : Config G c) (x : Fields G d) :
    ‖d.account u t V x‖ ≤ M*d.action t V x := by
  induction d generalizing u with
  | nil =>
    change ‖_ * energy V‖ ≤ M*(1*energy V); rw [one_mul,norm_mul,Real.norm_of_nonneg (energy_nonneg ..)]
    exact mul_le_mul_of_nonneg_right (hU _ (Nat.zero_le _)) (energy_nonneg ..)
  | @push m i S T d ih =>
    have hp : 0 ≤ tagEnergy S t.1 (T.drape (x ∘ Sum.inl)) V := (energy_estimate S _).nonneg _
    rw [account, action_push, mul_add]; refine (norm_add_le ..).trans (add_le_add ?_
      (ih t.2 (u := upβ u) (fun j hj => hU (j+1) (Nat.succ_le_succ hj)) _ _))
    rw [norm_mul,Real.norm_of_nonneg hp]
    exact mul_le_mul_of_nonneg_right (hU 1 (Nat.succ_le_succ (Nat.zero_le _))) hp

lemma account_sub (t : d.Tags) (u v : ℕ → ℝ) (V : Config G c) (x : Fields G d) :
    d.account (u-v) t V x = d.account u t V x - d.account v t V x := by
  induction d generalizing u v with
  | nil => exact sub_mul (u 0) (v 0) (energy V)
  | @push m i S T d ih =>
    simp only [account,Pi.sub_apply]
    rw [sub_mul, show upβ (u-v)= upβ u - upβ v from rfl, ih]; ring

/-- Single explicit volume-dependent bound, no compact choices in offset charges.
Not paying this in the scale-uniform η iteration. -/
def ceiling (top : Side) : {c : Side} → Descent top c → ℝ
  | _, .nil => (Fintype.card (Face (Per top)):ℝ)*2
  | _, .push S _ d => noiseCap S + ceiling top d
lemma action_bound (V : Config G c) (x : Fields G d) : d.action t V x ≤ ceiling n d := by
  induction d with
  | nil =>
    change (1:ℝ)*energy V ≤ ↑(Fintype.card (Face (Per n))) * 2
    rw [one_mul]
    exact (Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Face (Per n)))) =>
      (G.price_range (faceValue V i)).2)).trans_eq (by simp)
  | @push m i S T d ih =>
    rw [action_push]; exact add_le_add ((energy_estimate S _).bound V) (ih t.2 ..)

def offsetLoss (d : Descent n c) (M : ℝ) := Real.exp (M*ceiling n d)

private lemma exp_Lipschitz {x y b : ℝ} (hx : x ≤ b) (hy : y ≤ b) :
    ‖Real.exp x - Real.exp y‖ ≤ Real.exp b * ‖x-y‖ := by
  wlog H : x ≤ y generalizing x y
  · rw [norm_sub_rev, norm_sub_rev x y]; exact this hy hx (le_of_not_ge H)
  have h := Real.add_one_le_exp (x-y)
  have he : Real.exp (x-y) * Real.exp y = Real.exp x := by rw [← Real.exp_add,sub_add_cancel]
  have hf : Real.exp x ≤ Real.exp y := Real.exp_monotone H
  have hg := mul_le_mul_of_nonneg_right h (Real.exp_pos y).le
  rw [he] at hg; rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm, abs_sub_comm x y,
    abs_of_nonneg (sub_nonneg.mpr hf), abs_of_nonneg (sub_nonneg.mpr H)]
  refine le_trans (b:=Real.exp y * (y-x)) ?_
    (mul_le_mul_of_nonneg_right (Real.exp_monotone hy) (sub_nonneg.mpr H))
  linarith

variable (hU : d.Band M u) (hV : d.Band M v) (hi : d.Band δ (u-v))
    (f : Config G n → ℝ) (x : Fields G d)
include hU
lemma exponent_ceiling : ‖d.account u t 1 x‖ ≤ M*ceiling n d :=
  (total_charge t hU _ x).trans (mul_le_mul_of_nonneg_left (action_bound ..) (nonnegativeBand hU))

lemma roof : Real.exp (-d.account u t 1 x) ≤ offsetLoss d M :=
  Real.exp_le_exp.mpr (le_trans (neg_le_abs _) (exponent_ceiling t hU x))

lemma entry_floor : (offsetLoss d M)⁻¹ ≤ Real.exp (-d.account (G := G) u t 1 x) := by
  unfold offsetLoss; rw [← Real.exp_neg (M*ceiling ..)]; exact Real.exp_le_exp.mpr
    (neg_le_neg ((le_abs_self _).trans (exponent_ceiling t hU x)))

lemma uniform : ‖d.resetTerms u f t x‖ ≤ offsetLoss d M * ‖f (d.fine 1 x)‖ := by
  rw [resetTerms,norm_mul]; exact mul_le_mul_of_nonneg_right ((Real.norm_of_nonneg (Real.exp_pos _).le).trans_le
    (roof t hU x)) (norm_nonneg _)
include hV hi
lemma reset_cost : ‖(d.resetTerms u f t - d.resetTerms v f t) x‖ ≤
    (offsetLoss d M * δ) * ‖d.action t 1 x * f (d.fine 1 x)‖ := by
  have hu := (neg_le_abs _).trans (exponent_ceiling t hU x)
  have hv := (neg_le_abs _).trans (exponent_ceiling t hV x)
  have he := total_charge t hi 1 x
  rw [account_sub] at he
  simp only [Pi.sub_apply,resetTerms,← sub_mul,norm_mul,Real.norm_of_nonneg (action_nonneg d t ..)]
  unfold offsetLoss
  refine (mul_le_mul_of_nonneg_right ((exp_Lipschitz hu hv).trans
    (mul_le_mul_of_nonneg_left (le_trans ?_ he) (Real.exp_pos _).le)) (norm_nonneg _)).trans_eq ?_
  · rw [show - d.account u t 1 x - - d.account v t 1 x= -(d.account u t 1 x - d.account v t 1 x) by ring,norm_neg]
  ring

variable (F : Continuous f) (ha : 0 < a)
include h F ha

private lemma costOne :
    ‖region t (d.resetTerms u f t) univ a - region t (d.resetTerms v f t) univ a‖ ≤
      (offsetLoss d M * δ) * region t (fun x => ‖d.action t 1 x * f (d.fine 1 x)‖) univ a := by
  let Y i := d.resetTerms i f t
  let W := (offsetLoss d M * δ) • (fun x => ‖d.action t 1 x * f (d.fine 1 x)‖)
  have hw := env_realScale (env_norm ((env_action t h).mul (env_field d f F))) (offsetLoss d M * δ)
  rw [← region_sub t h (reset_env u h F t) (reset_env v h F t),← region_scale]
  exact (region_le_abs t _ ha univ).trans (monotonicity t h (env_norm ((reset_env u h F t).add (reset_env v h F t).neg)) hw
    (fun x => reset_cost t hU hV hi f x) ha)

def fullLoss (d : Descent n c) (f : Config G n → ℝ) := ∑ t : d.Tags, region t (fun x => ‖d.action t 1 x * f (d.fine 1 x)‖) univ

omit t in
lemma change_bill : ‖generation d u f a - generation d v f a‖ ≤ offsetLoss d M*δ * fullLoss d f a := by
  simp only [fullLoss,generation, Finset.sum_apply, ← Finset.sum_sub_distrib, Finset.mul_sum]
  exact (norm_sum_le ..).trans (Finset.sum_le_sum fun i _ => costOne h i hU hV hi f F ha)

omit hV hi F
omit h hU ha in
lemma account_zero (x : Fields G d) : d.account 0 t (1:Config G c) x = 0 := by
  apply norm_eq_zero.mp
  have he : d.Band 0 0 := fun i _ => by simp
  exact le_antisymm (le_trans (total_charge (M:=0) t he 1 x) (by simp)) (norm_nonneg _)

omit h hU ha in
private lemma reset_zero_unit (x : Fields G d) : d.resetTerms 0 (G:=G) 1 t x = 1 := by
  simp only [resetTerms,account_zero,neg_zero,Pi.one_apply,Real.exp_zero,mul_one]

omit t in
lemma floor_cost : (offsetLoss d M)⁻¹ * generation (G := G) d 0 1 a ≤ generation (G := G) d u 1 a := by
  simp only [generation, Finset.sum_apply, Finset.mul_sum,← region_scale]
  refine Finset.sum_le_sum fun i _ => monotonicity i h (env_realScale (reset_env _ h (g:=1) continuous_const i) _)
    (reset_env u h (g:=1) continuous_const i) ?_ ha
  intro x
  rw [Pi.smul_apply, smul_eq_mul, reset_zero_unit, mul_one]
  unfold resetTerms; rw [Pi.one_apply,mul_one]; exact entry_floor i hU x

omit ha hU h
lemma floor_positive (h : d.OK G) (u : ℕ → ℝ) (ha : 0 < a) : 0 < generation (G:=G) d u 1 a := by
  apply pos_of_mul_pos_right (a:= d.scalar G (offset u a) * a ^ Module.finrank ℝ (Coordinates G d))
  · rw [prefactor_equation (g := 1) u h (fun _ _ => rfl) continuous_const ha, weighted_unit]; exact positive _ h _
  exact mul_nonneg (scalar_pos ..).le (by positivity)

lemma action_grade (h : d.OK G) : RadialOrder 2 ((d.action (G := G) t 1) ∘ d.tablePath) := by
  let f := d.phase G t; have he := stationary h t; intro u
  apply bill_of_grade (directions he.smooth u); intro i hi
  interval_cases i
  · rw [jet_zero]; exact he.base0
  exact he.base1 u

section
variable {w : ℕ} (P : ChartRatio G) (R : LocalRatio P) (H : d.Room G) (hF : d.Testable f)
    (hG : d.grade f w) (gV : d.Band M v)
include R H hF hG
lemma field_offset_grade : Bill (w+2) (fullLoss d f) := by
  refine bill_sum _ _ (fun i _ => ?_); rw [Nat.add_comm]
  apply absolute_grade (f := fun x => d.action i 1 x * f (d.fine 1 x)) (w:=2+w) i _ R H ((stationary (room_ok d H) i|>.smooth).mul hF.smooth)
    (fun x => bill_mul (action_grade i (room_ok d H) x) (hG x))
  exact (env_action i (room_ok d H)).mul (env_field d f hF.neat)

-- range of inverse β shifts finite geometry; hG test-local L1 bills
include gV
/-- Uniformly over the **actual** u in the band. Formal side fixed `v`. At `v=0` sufficient through
requested r=1. In the normalized moment the inverse-coupling mismatch pays one `a²` credit,
with respect to normalization on the *same descent*, even for the top grade and regardless of
whether `u` is smooth. Constants after finite cutoff/period. `a^(w+2) * δ`. -/
theorem conditioned_offset_grade : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ a in Tested.germ, ∀ u δ,
    d.Band M u → d.Band δ (u-v) →
      ‖d.conditioned (offset u a) f 1 - d.conditioned (offset v a) f 1‖ ≤ C*a^(w+2)*δ := by
  let W := offsetLoss d M; have hW : 0 < W := Real.exp_pos _
  let p := bareRank P d 0 1 0; have hp : 0 < p := pivot P R 0 H
  let f' (u a) := generation d u f a; let g (u a) := generation d u (G:=G) 1 a
  obtain ⟨Cf,hCf,wF⟩ := generation_grade P R H v hF hG
  obtain ⟨Ce,hCe,wE⟩ := field_offset_grade f P R H hF hG
  let h' := unit_test (G:=G) d;
  obtain ⟨Cp,hCp,wP⟩ := field_offset_grade (w:=0) (f:=1) P R H h' (fun x => (directions h'.smooth x).bounded)
  have hx : Tendsto (g 0) Tested.germ (𝓝 p) := (bare_comparison P R 0 H h').tendsto_first
  let c := W⁻¹*(p/2); have hc : 0<c := by unfold c; positivity
  refine ⟨W*Ce/c + W*Cp*Cf/(c*c),by positivity,?_⟩
  filter_upwards [hx.eventually (lt_mem_nhds (half_lt_self hp)), wF, wE, wP,eventually_pos] with a ht Hf He Hp ha u δ hu hv
  have hh : p/2 ≤ g 0 a := (show p/2 < g 0 a from ht).le
  let f₁ := f' u a; let f₂ := f' v a; let g₁ := g u a; let g₂ := g v a
  have hg₁ : c ≤ g₁ := (mul_le_mul_of_nonneg_left hh (inv_pos.mpr hW).le).trans (floor_cost (room_ok d H) hu ha)
  have hg₂ : c ≤ g₂ := (mul_le_mul_of_nonneg_left hh (inv_pos.mpr hW).le).trans (floor_cost (room_ok d H) gV ha)
  have hδ : 0 ≤ δ := nonnegativeBand hv; have hWδ : 0 ≤ W*δ := mul_nonneg hW.le hδ
  have hfN : ‖f₁-f₂‖≤ W*δ*(Ce*a^(w+2)) := le_trans (change_bill (room_ok d H) hu gV hv f hF.neat ha)
    (mul_le_mul_of_nonneg_left ((le_abs_self _).trans He) hWδ)
  have hgN : ‖g₂-g₁‖≤ W*δ*(Cp*a^2) := by
    rw [norm_sub_rev]
    exact le_trans (change_bill (room_ok d H) hu gV hv 1 continuous_const ha)
      (mul_le_mul_of_nonneg_left ((le_abs_self _).trans Hp) hWδ)
  rw [conditioned_eq u (room_ok d H) hF.invariant hF.neat ha, conditioned_eq v (room_ok d H) hF.invariant hF.neat ha]; change ‖f₁/g₁-f₂/g₂‖ ≤ _
  have hg₁' := lt_of_lt_of_le hc hg₁; have hg₂' := lt_of_lt_of_le hc hg₂
  rw [show f₁/g₁-f₂/g₂=(f₁-f₂)/g₁+(g₂-g₁)*f₂/(g₁*g₂) by field_simp; ring]
  apply (norm_add_le ..).trans
  rw [norm_div,norm_div,norm_mul,norm_mul,Real.norm_of_nonneg hg₁'.le,Real.norm_of_nonneg hg₂'.le]
  refine (add_le_add (div_le_div₀ (c:=W*δ*(Ce*a^(w+2))) (by positivity) hfN hc hg₁)
      (div_le_div₀ (c:=(W*δ*(Cp*a^2))*(Cf*a^w)) (by positivity) (by gcongr) (by positivity : 0<c*c) (by gcongr))).trans_eq ?_
  rw [pow_add]; ring
end
end YM.RGComparison.Core16.Descent
