import YM.RG12.Canonical.FromFrames

/-!
# Evaluate along a simple geometric set of radii, comparison age supplied by any Family

Uses no quantitative clock/scheduling hypotheses. Just establishes that the hypotheses on
that configuration scope would suffice (all unit-log-spaced radii, and comparing to columns
on a comparable-radius window).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Sample
open Function Filter RG Source Lattice Real
open scoped Topology BigOperators
variable {G : Gauge}

def age (i : ℕ) := ((i:ℝ)+2) -- coe syntax?
def length (i : ℕ) := Real.exp (- (i:ℝ))
def ratio (_ : ℕ) := Real.exp 1

variable (C : Family G)
def atMesh (k : ℕ) := ⌊C.S.scale k⌋₊

lemma sampled_tends : Tendsto (atMesh C) atTop atTop := tendsto_atTop.mpr fun i=>by
  filter_upwards [C.S.divergent.eventually_ge_atTop (i:ℝ)] with k hk using
    (Nat.le_floor hk)

lemma samples_clock {K:ℝ} : ∃ n₀:ℕ, ∀ i:ℕ,n₀ ≤ i→
    K ≤ age i ∧ age i + 1 ≤ age (i+1) ∧ age (i+1) /age i ≤ age i := by
  obtain ⟨i,h⟩:= exists_nat_gt K; refine ⟨i,fun n hn=>?_⟩
  unfold age; push_cast
  have he : (i:ℝ)≤n:= by exact_mod_cast hn
  refine ⟨by linarith only [h,he],by linarith, (div_le_iff₀ (by positivity)).mpr ?_⟩
  nlinarith only [Nat.cast_nonneg (α:=ℝ) n]

lemma samples_spacing (i : ℕ) : 0 < length i ∧ 1 ≤ ratio i ∧ length (i+1)=length i /ratio i := by
  unfold length ratio; push_cast; rw [neg_add,Real.exp_add,Real.exp_neg 1]
  exact ⟨Real.exp_pos _, Real.one_le_exp zero_le_one, div_eq_mul_inv .. |>.symm⟩

lemma enough_stops (hG:G.Simple) (e n : ℕ) : ∀ᶠ k in atTop,
    Nonempty (Stop C age length n (atMesh C) k (e+2)) := by
  let B:= C.path.levels.clock; let b:=G.slopeConstant; let z:=B.bar
  have hb:0<b:=Gauge.slopeConstant_pos hG; have hv:=hat_grows (C:=C) hG
  filter_upwards [C.S.divergent.eventually_ge_atTop 0,hv.eventually_ge_atTop 1,
    hv.eventually_ge_atTop (b⁻¹+|z/b|+2),hv.eventually_ge_atTop (Real.exp 1), (sampled_tends C).eventually_ge_atTop n]
    with k hk hp hx hf hn
  let t:= C.S.scale k; have ht : B.hatBeta k=z+b*t:=rfl
  let a:= C.S.a k; have hh :0<a := C.S.a_pos _
  have h(i)(he:1 ≤ i) : B.hatBeta k ≤ B.hatBeta k^i:=by simpa only [pow_one] using pow_le_pow_right₀ hp he
  have he:1+1 ≤ e+2:= by omega
  have h1:=h (e+2) (by omega)
  have ha: Real.exp (- t)=a:=by rw [Real.exp_neg,show Real.exp t=a⁻¹ from Real.exp_log (inv_pos.mpr hh)]; simp
  refine ⟨hn, ?_, ?_, ?_⟩ -- Nonempty Stop has one Stop not 4? constructor elaboration angle nested!
  · let p:=B.hatBeta k; unfold age atMesh
    have hz : |z/b|≥0:=abs_nonneg _; have hr:= Nat.floor_le hk
    have H' : p≥ b⁻¹+|z/b|+2:=hx
    have hx : t= b⁻¹*p-z/b:=by dsimp only [p]; rw [ht]; field_simp; ring
    calc
      _ ≤ t+2:=by linarith only [hr] -- t def rfl
      _ ≤ (b⁻¹+|z/b|+2)*p:= by
        rw [hx]; have h2 : |z/b|+2≤(|z/b|+2)*p := le_mul_of_one_le_right (by linarith only [hz]) hp; linarith only [h2,neg_le_abs (z/b)]
      _ ≤ p^(2:ℕ):=by rw [pow_two]; gcongr
      _ ≤ _:= pow_le_pow_right₀ hp he
  · change _ ≤ a * _; unfold length atMesh
    calc
       _ ≤ Real.exp (-t+1):= Real.exp_le_exp.mpr (by have h:=Nat.lt_floor_add_one t; linarith)
       _ = a * Real.exp 1:= by rw [Real.exp_add,ha]
       _ ≤ _:=mul_le_mul_of_nonneg_left (hf.trans h1) hh.le
  change a ≤ length _ * _
  have hx:a≤length (atMesh C k):= ha ▸ (Real.exp_le_exp.mpr (neg_le_neg (Nat.floor_le hk)))
  exact hx.trans (le_mul_of_one_le_right (hh.le.trans hx) (hp.trans h1))
end YM.RG12.Sample
