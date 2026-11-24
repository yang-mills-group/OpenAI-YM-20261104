import YM.GradedFar.CropFields
import YM.GradedFar.Width
/-!
# Spend the pointwise ingredients of (M.2) first (the `RoundMeter QScale` argument)

Including the finite-product omission shown in `GradedFar.CropFields`. Here ``Today`` is an
arbitrary received ordinary moment map; results are arithmetic/transport lemmas for use at the
genuine price claims in the graded far-field argument. NOTE THAT THIS FILE BY ITSELF IS NOT A PHYSICAL
PRICE ON THAT MOMENT MAP. In particular the remainder estimate requested on Today on the right
fields must come from a hypothesis (G.9) about that very map and these constant-leg tests; and
we don't infer the norm bound and price of replacing the actual field maps by projections here.
See physical application.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Function Filter Set PowerSeries
open XSpace XSpace.Normalize XSpace.Structure1 Scale
open Dframe O O.Score O.Enh
open scoped Topology BigOperators Classical

variable {G : Gauge} {n m l h : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}
    {A : Arenas G} {F : ℝ → Frames G} {ψ : ℝ → PowerSeries ℂ}

lemma uses_field {B : Sec G l →ₗ[ℂ] Sec G h} {v : Sec G l} {C : ℝ} (hC : 0 ≤ C)
    (hb : opField B ≤ C) (hv : width v ≤ 1) : width (B v) ≤ C := by
  exact (op_use ..).trans ((mul_le_mul hb hv (width_nn _) hC).trans_eq (mul_one _))

section pen
variable (hd : Through l d) (he : Through l e)
/-- Annotation for summing field costs in this convention (D_E). -/
def power (e : Fin m → ℕ) := ∑ j, e j
lemma pow_all (T B : ℝ) : (∏ i : Fin m, B*T^(e i)) = B^m * T^power e := by
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]; simp [power]

-- total degree p; field approximation order q≥p in use
variable {x : Points n} {y : Points m} (u : Inputs G d) (v : Inputs G e)
    (Today : Both G d e) {T B δ Q b z E : ℝ} {p q : ℕ}
local notation "η" => (-Real.log T)
local notation "M'" => constantCrop A η hd he x y p z u
local notation "Ψ" => cropK F η q z
set_option maxHeartbeats 300000 in
lemma replacement_transport
    -- raw reports received at H_r on all slots (Near arguments here fixed to u, Far still arbitrary)
    (hv : Box v 1) (hQ : 0 ≤ Q) (hf : ∀ v, Box v 1 → ‖M' v‖ ≤ Q) (hb : 0 ≤ b)
    (h0 : ∀ v, Box v 1 → ‖Today u v - M' v‖ ≤ b)
    -- costs of actual Far maps `X i` and replacing by the better predictors
    (X : ∀ i, Sec G (e i) →ₗ[ℂ] Sec G (e i))
    (hT : 1 ≤ T) (hB : 1 ≤ B) (hp : ∀ i, opField (X i) ≤ B*T^(e i))
    (hq : 0 ≤ δ) (hlt : δ ≤ 1)
    (hδ : ∀ i, opField (X i - Ψ (e i)) ≤ δ)
    (hE : ‖recropped hd he A F η p q z x y u v‖ ≤ E) :
    ‖Today u (fun i => X i (v i)) - crop p z (fullSeries A F η hd he x y u v)‖ ≤
      (b + Q*((m:ℝ)*δ))*(((B+1)^m)*T^power e) + E := by
  let g (i : Fin m) := (B+1)*T^(e i)
  let w : Inputs G e := fun i => X i (v i)
  let w' := cropArguments F η q z v
  have h2 (i : Fin m) : 1 ≤ T^(e i) := one_le_pow₀ hT
  have h1 (i) : 1 ≤ g i := one_le_mul_of_one_le_of_one_le (by linarith) (h2 i)
  have hW (i) : width (w i) ≤ B*T^(e i) := uses_field (B:=X i) (v:=v i) (by positivity) (hp i)
    ((boxes zero_le_one).mp hv i)
  have hX (i) : width (w i) ≤ g i := (hW i).trans (by dsimp [g]; gcongr; linarith)
  have hdif (i) : width (w i-w' i) ≤ δ := uses_field (B:=X i - Ψ (e i)) (v:=v i) hq (hδ i) ((boxes zero_le_one).mp hv i)
  have hX' (i) : width (w' i) ≤ g i := by
    have hu := width_sub (w' i) (w i); rw [width_sub_symm] at hu
    unfold g; linarith [hW i, hdif i, h2 i]
  let a := Today u w; let c := M' w; let c' := M' w'; let d := crop p z (fullSeries A F η hd he x y u v)
  have hi : ‖a-c‖ ≤ b * ∏ i, g i := by
    exact (box_apply (Today u-M') hb h0 w).trans (mul_le_mul_of_nonneg_left (Finset.prod_le_prod
      (fun i _=> width_nn _) (fun i _=> hX i)) hb)
  have hh : ‖c-c'‖ ≤ Q*((m:ℝ)*δ*∏ i, g i) := box_sub (M') hQ hf w w' hX hX'
    (fun i=> (hdif i).trans (le_mul_of_one_le_right hq (h1 i)))
  rw [recropped_value] at hE
  calc
    ‖a-d‖ ≤ ‖a-c‖ + ‖c-c'‖ + ‖c'-d‖ := (norm_sub_le_norm_sub_add_norm_sub a c' d).trans <|
      add_le_add (norm_sub_le_norm_sub_add_norm_sub a c c') (le_refl _)
    _ ≤ _ := (add_le_add (add_le_add hi hh) hE).trans_eq (by unfold g; rw [pow_all]; ring)

/-- Uniform (η) prefix of T logarithms purchased, fields/dial applied at the chosen larger
order `q ≥ p`. Includes the price of the replacement of the actual field operations with their
own costs through their caps. No requirement that the true discrepancy itself pay that same
price as a coefficient before evaluation. Use in physical application **also for every center**.
The z argument uses only the `measured_budget` bridge exactly as in second. -/
theorem sale (H : Canon.Physical A ψ F) (law : Scale.Law A ψ F)
    {K : Set (Points n)} {S : Set (Points m)}
    (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ Outside m)
    (hp : p ≤ q) {B Q δ : ℝ} (hB : 1 ≤ B) (hQ : 0 ≤ Q) (hq : 0 ≤ δ) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∀ᶠ T in atTop,
    ∀ x ∈ K, ∀ y ∈ S, ∀ (z g : ℝ) (u : Inputs G d) (v : Inputs G e), 0 ≤ g →
    |z| ≤ 1 → |z| ≤ 2*g → Box u 1 → Box v 1 → δ*g^(p+1) ≤ 1 → ∀ Today : Both G d e,
    (∀ v, Box v 1 → ‖Today u v - constantCrop A (-Real.log T) hd he x y p z u v‖ ≤
      Q*(g^(p+1))*(1+Real.log T)^k) →
    ∀ X : ∀ i, Sec G (e i) →ₗ[ℂ] Sec G (e i),
    (∀ i, opField (X i) ≤ B*T^(e i)) →
    (∀ i, opField (X i-cropK F (-Real.log T) q z (e i)) ≤ δ*g^(p+1)) →
      ‖Today u (fun i => X i (v i)) - crop p z (fullSeries A F (-Real.log T) hd he x y u v)‖ ≤
          C*T^power e*g^(p+1)*(1+Real.log T)^a := by
  let I := Domain d e G K S 1
  obtain ⟨C,hC,j,H'⟩ := Omitted.budget (buys_recrop (I:=I) hd he p q H law hK hx hS hy (x:=Domain.x)
    (y:=Domain.y) Domain.hz hp zero_le_one Domain.hu Domain.hv)
  obtain ⟨D,hD,lD,hm⟩ := raw_rain (I:=I) hd he p H hK hx hS hy (x:=Domain.x) (y:=Domain.y) Domain.hz
    zero_le_one Domain.hu Domain.hv
  let iA := k+j+lD
  refine ⟨((Q+D*((m:ℝ)*δ))*(B+1)^m + 2^(p+1)*C), by positivity, iA,?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually (H'.and hm), eventually_ge_atTop (1:ℝ)] with T ht hT
  intro x hX y hY z g u v hg hz hz' hu hv hδ L hf X hhi hX'
  let M := 1+Real.log T
  have h₁ : 1 ≤ M := le_add_of_nonneg_right (Real.log_nonneg hT)
  have hi : ∀ v', Box v' 1 → ‖constantCrop A (-Real.log T) hd he x y p z u v'‖ ≤ D*M^lD := by
    intro v' h
    simpa only [I,M,post,neg_zero,zero_mul,Real.exp_zero, mul_one]
      using (ht.2 (⟨⟨x,hX⟩,⟨y,hY⟩,u,v',hu,h,z,hz⟩ : Domain d e G K S 1))
  have he' := replacement_transport hd he u v L hv (by positivity : 0 ≤ D*M^lD) hi (by change 0 ≤ Q*g^(p+1)*M^k; positivity) hf X hT hB hhi (mul_nonneg hq (pow_nonneg hg _)) hδ hX'
    (ht.1 (⟨⟨x,hX⟩,⟨y,hY⟩,u,v,hu,hv,z,hz⟩: I))
  apply he'.trans
  dsimp only; rw [post,neg_zero,zero_mul,Real.exp_zero,mul_one]
  have h₂ : 1 ≤ T^power e := one_le_pow₀ hT
  change (Q*g^(p+1)*M^k + (D*M^lD)*((m:ℝ)*(δ*g^(p+1))))*((B+1)^m*T^power e) +
    |z|^(p+1)*(C*M^j) ≤ _*M^iA
  calc
    _ ≤ (Q*g^(p+1)*M^iA + (D*M^iA)*((m:ℝ)*(δ*g^(p+1))))*((B+1)^m*T^power e) +
      (2*g)^(p+1)*(C*M^iA) := by dsimp only [iA]; gcongr <;> omega
    _ ≤  (Q*g^(p+1)*M^iA + (D*M^iA)*((m:ℝ)*(δ*g^(p+1))))*((B+1)^m*T^power e)+(2*g)^(p+1)*(C*M^iA)*T^power e :=
      add_le_add (le_refl _) (le_mul_of_one_le_right (by positivity) h₂)
    _ = _ := by rw [mul_pow]; ring
end pen
end YM.FVA2.GradedFar
