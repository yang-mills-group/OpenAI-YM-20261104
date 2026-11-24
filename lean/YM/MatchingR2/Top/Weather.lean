import YM.MatchingR2.Top.Health

/-!
# Eventually on realized schedule

No waiting till after a period chosen. Some constants from analysis are post block and thus
require a *new* gate aligning with the other spatial ones. Here derive several physical
alignment estimates *without* a gate. True coupling from the fine rep (N,p,N). Do not confuse
post-L estimates with a uniform result in m.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingR2.Top
open RG Filter Function Lattice Wilson Tree Pressure
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} (H: History G)
set_option quotPrecheck false
local notation "A" => H.levels
local notation "T" => H.levels.clock
local notation "S" => H.S
-- no volume preclusion beyond this history. use Gentle and administrative conditions only.
lemma hat_large (h:G.Simple) : Tendsto ((T).hatBeta) atTop atTop := by
  have he := (S).divergent.const_mul_atTop (Gauge.slopeConstant_pos h)
  exact tendsto_atTop_add_const_left atTop _ he
lemma warmer (h:G.Simple) : ∀ᶠ m:ℕ in atTop, ∀ p : ℕ,
    2* (T).hatBeta (m+1) ≤ (((S).side m p).val:ℝ)^2 := by
  let k := G.slopeConstant
  let y := (S).scale
  let D := fun m => ((S).denominator m).val
  have he m : y m = Real.log (D m:ℝ):= by simp [y, Schedule.scale, Schedule.a, D]
  have hd (m p : ℕ) : D m ≤ ((S).side m p).val := Nat.le_mul_of_pos_left _ ((S).period p).pos
  have hg : 0<k := Gauge.slopeConstant_pos h
  have hu:= (S).divergent
  have hb:= (A).fits.mesh
  filter_upwards [hb.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1)), hu.eventually_ge_atTop
    (2*(T).bar + 4*k + 1)] with m hm hY
  intro p; let L := ((S).block m).val
  let v : ℝ := D m; let w := y m
  have h0:(0:ℝ) < w := lt_of_lt_of_le (by positivity [(T).bar_pos]) hY
  have hw : y (m+1) ≤ 2*w := by
    have hl : Real.log (L:ℝ) / w ≤ 1 := hm
    rw [div_le_iff₀ h0] at hl
    unfold y; rw [Schedule.scale_succ]; change w + Real.log (L:ℝ) ≤ _
    linarith
  have hv : 1+w ≤ v := by
    unfold w v; rw [he]; have hi:=Real.log_le_sub_one_of_pos (by exact_mod_cast ((S).denominator m).property : 0<(D m:ℝ)); linarith
  have hT := (T).bar_pos
  have hy : 2*(T).bar+4*k+1 ≤ w:=hY
  have hm': (v:ℝ) ≤ ((S).side m p).val:= by unfold v; exact_mod_cast hd m p
  calc
    _ ≤ 2*((T).bar+k*(2*w)) := by change 2*((T).bar+k*y (m+1))≤_; gcongr
    _ ≤ v^2 := by nlinarith
    _ ≤ _ := pow_le_pow_left₀ (by linarith) hm' 2

lemma step_shape : ∀ᶠ m:ℕ in atTop, ∀ p : ℕ, Bid.Larger ((T).op m p) (G:=G) := by
  let J := (T).J
  let D := fun m => ((S).denominator m).val
  let a (m p:ℕ):= ((S).side m p).val
  let L m := ((S).block m).val
  have hp m : 0<D m:= ((S).denominator m).property
  have hd (m p : ℕ) : D m ≤ a m p := Nat.le_mul_of_pos_left _ ((S).period p).pos
  have he (m p) : a (m+1) p=a m p*L m:= ((T).op m p).sizes
  have hJ m : J (m+1) ≤ J 0+(m+1) := by
    induction m with
    | zero => exact (A).fits.stepSlow 0
    | succ m ih => have hv : J (m+1+1) ≤ J (m+1)+1:= (A).fits.stepSlow _; omega
  have hL m : 3 ≤ L m:= (S).block_large m
  have hK m : D (m+1)=D m*L m:= PNat.mul_coe ..
  have hP m : 1+m^2 ≤ D m:= by
    induction m with
    | zero => exact le_of_eq rfl
    | succ m ih => rw [hK]; have hx:= Nat.mul_le_mul ih (hL m); nlinarith
  -- avoid needing Large proof from Pledge
  filter_upwards [eventually_ge_atTop (100*(J 0+9))] with m hm p
  refine ⟨((A).blocks m p).branches,?_,?_⟩
  · change 100*((J (m+1)+3)*L m+4*L m) ≤ a (m+1) p; rw [he,← add_mul,← mul_assoc]; apply Nat.mul_le_mul_right; have := (hP m).trans (hd m p); have h:=hJ m; nlinarith
  exact lt_of_lt_of_le (show 1 < 1+m^2 by nlinarith) ((hP m).trans (hd m p))
lemma warm (h:G.Simple) (hH:H.Selected) : ∀ᶠ m:ℕ in atTop, ∀ p:ℕ, 1 ≤ H.β (m+1) p (m+1) ∧
    Real.sqrt (H.β (m+1) p (m+1)) ≤ ((S).side m p).val := by
  have hU := (hat_large H h).comp (show Tendsto (fun (m:ℕ)=>m+1) atTop atTop from tendsto_add_atTop_nat 1)
  filter_upwards [warmer H h,hU.eventually_ge_atTop 2] with m hm hl p
  have he := hH.represents (m+1) p (m+1) le_rfl
  constructor
  · exact le_trans (b:=(T).hatBeta (m+1)/2) (by change 2 ≤ (T).hatBeta (m+1) at hl; linarith) he.band.1
  exact Real.sqrt_le_iff.mpr ⟨Nat.cast_nonneg _,he.band.2.trans (hm p)⟩
end YM.MatchingR2.Top
