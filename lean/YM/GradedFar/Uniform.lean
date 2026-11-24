import YM.GradedFar.Cancellation
/-!
# Now price the measurements on all the `Sec` input balls

Use the sup norm in Dframe bases. Can take any finite radius in each
of the estimates. The domain includes exactly the `x,y` shape parameters in
those units. The cost analysis (F.O) and (F.1) after conversion was on this
already; now allow also simultaneous variation in all field directions. No bound on
separate Minkowski/Sobolev norms of Far tests is needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Function Filter Set PowerSeries
open XSpace XSpace.Normalize XSpace.Structure1 Scale
open Dframe O O.Score O.Enh
open scoped Topology BigOperators Classical

variable {G : Gauge} {n m l h : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}
variable {A : Arenas G} {F : ℝ → Frames G}
def ope (A : Arenas G) (u : Inputs G d) (x : Points n) (q : Q G) :=
  ∑ b : Picks G d, PowerSeries.C (multipliers u b) * Canon.FarCoefficients A (indexScan b) x q

section lift
variable (η : ℝ) (hd : Through l d) (he : Through l e) (x : Points n) (y : Points m)
    (u : Inputs G d) (v : Inputs G e)

lemma ope_basis (A : Arenas G) (p : Picks G d) (x : Points n) (q : Q G) :
    ope A (basisWord p) x q = Canon.FarCoefficients A (indexScan p) x q := by
  unfold ope; simp_rw [basis_delta]; classical simp

lemma fullSeries_near (A : Arenas G) (F : ℝ → Frames G) :
    fullSeries A F η hd he x y u v =
      ∑ b : Picks G d, PowerSeries.C (multipliers u b) * fullSeries A F η hd he x y (basisWord b) v := by
  ext k
  simp_rw [map_sum, coeff_C_mul, fullSeries, coeff_mk]
  rw [basis_sum (withFar ..) u]; simp only [sum_apply, smul_apply, smul_eq_mul]

lemma fullSeries_far (A : Arenas G) (F : ℝ → Frames G) :
    fullSeries A F η hd he x y u v =
      ∑ b : Picks G e, PowerSeries.C (multipliers v b) * fullSeries A F η hd he x y u (basisWord b) := by
  ext k; simp_rw [map_sum, coeff_C_mul, fullSeries, coeff_mk]
  exact basis_sum _ v

-- use inside double sum, etc.
lemma replacementSeries_far (A : Arenas G) (F : ℝ → Frames G) (hh : h ≤ l) (a : Sec G h) :
    replacementSeries A F η hh he y a v =
      ∑ b : Picks G e, PowerSeries.C (multipliers v b) * replacementSeries A F η hh he y a (basisWord b) :=
  fullSeries_far η (d:=Output h) (fun _ => hh) he (0:Points 1) y (fun _ => a) v A F

def tailSeries (A : Arenas G) (F : ℝ → Frames G) (η : ℝ) (hd : Through l d) (he : Through l e)
    (hh : h ≤ l) (x : Points n) (y : Points m) (u : Inputs G d) (v : Inputs G e) :=
  fullSeries A F η hd he x y u v - ∑ q : Toon G h, ope A u x (Dframe.flash q) *
    replacementSeries A F η hh he y (theory q) v

lemma tailSeries_near (hh : h ≤ l) :
    tailSeries A F η hd he hh x y u v =
      ∑ b : Picks G d, PowerSeries.C (multipliers u b) * tailSeries A F η hd he hh x y (basisWord b) v := by
  unfold tailSeries
  rw [fullSeries_near η hd he x y u v]
  simp_rw [ope_basis, mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  simp_rw [ope, Finset.sum_mul, mul_assoc, Finset.mul_sum]; rw [Finset.sum_comm]

lemma tailSeries_far (hh : h ≤ l) :
    tailSeries A F η hd he hh x y u v =
      ∑ b : Picks G e, PowerSeries.C (multipliers v b) * tailSeries A F η hd he hh x y u (basisWord b) := by
  unfold tailSeries
  rw [fullSeries_far η hd he x y u v]
  simp_rw [mul_sub]; rw [Finset.sum_sub_distrib]; congr 1
  simp_rw [replacementSeries_far η he y v _ _ hh, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_left_comm ..
end lift

section bounds
-- state uniformity on all parameters with family I
variable {I : Type} {p : ℕ} {a L : ℝ}

lemma charge_multipliers {u : I → Inputs G d} (p b) (hL : 0 ≤ L) (hu : ∀ i, Box (u i) L) :
    ChargeP p 0 (fun (i : I) (_ : ℝ) => PowerSeries.C (multipliers (u i) b)) :=
  ChargeP.constants (Rain.cash ⟨ L^n, fun i => multipliers_le hL _ _ (hu i) ⟩)

lemma lift_charge {f : I → ℝ → Inputs G d → PowerSeries ℂ}
    (hm : ∀ i s u, f i s u = ∑ b : Picks G d, PowerSeries.C (multipliers u b) * f i s (basisWord b))
    (hf : ∀ b : Picks G d, ChargeP p a (fun i s => f i s (basisWord b))) {u : I → Inputs G d}
    (hL : 0 ≤ L) (hu : ∀ i, Box (u i) L) : ChargeP p a (fun i s => f i s (u i)) := by
  simp_rw [show ∀ i s, f i s (u i) = _ from fun i s => hm i s (u i)]
  exact ChargeP.sum _ fun b _ => ChargeP.times (charge_multipliers _ _ hL hu) (hf b)

variable {ψ : ℝ → PowerSeries ℂ} (H : Canon.Physical A ψ F) (law : Scale.Law A ψ F)
    {K : Set (Points n)} {S : Set (Points m)}
    (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ Outside m)

include H
include hK hx in
theorem uniform_opeCoeff (q : Q G) (p : ℕ) (hL : 0 ≤ L) :
    ∃ C : ℝ, ∀ x ∈ K, ∀ u : Inputs G d, Box u L → ‖coeff p (ope A u x q)‖ ≤ C := by
  choose C hC using fun b : Picks G d => demand_opeCoeff H hK hx (indexScan b) q p
  refine ⟨ ∑ b : Picks G d, L^n * C b, ?_⟩
  intro x hX u hu
  simp_rw [ope, map_sum, coeff_C_mul]
  refine (norm_sum_le ..).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [norm_mul]; exact mul_le_mul (multipliers_le hL u b hu) (hC b x hX) (norm_nonneg _) (pow_nonneg hL _)

include law
variable {x : I → ↥K} {y : I → ↥S} (hd : Through l d) (he : Through l e)
    {u : I → Inputs G d} {v : I → Inputs G e}

include hS hy in
theorem uniform_replacement_charge (hh : h ≤ l) (p : ℕ) (q : Toon G h) (hL : 0 ≤ L) (hv : ∀ i, Box (v i) L) :
    ChargeP (p+1) (heft (Dframe.flash q) : ℝ) (fun i s => replacementSeries A F (-s) hh he (y i).val
      (theory q) (v i)) := by
  refine lift_charge (f:=fun i s v => replacementSeries A F (-s) hh he (y i).val (theory q) v)
    (fun i s v => replacementSeries_far (-s) he (y i).val v A F hh (theory q)) (fun b => ?_) hL hv
  exact ChargeP.pull (replacement_charge_basis H law hS hy (indexScan b) he (Dframe.flash q) hh
    (size_le q) (boundedByCaps b) p) y
include hK hx hS hy

theorem uniform_full_charge (p : ℕ) (hL : 0 ≤ L) (hu : ∀ i, Box (u i) L) (hv : ∀ i, Box (v i) L) :
    ChargeP (p+1) 0 (fun i s => fullSeries A F (-s) hd he (x i).val (y i).val (u i) (v i)) := by
  refine lift_charge (f:=fun i s u => fullSeries A F (-s) hd he (x i).val (y i).val u (v i))
    (fun i s u => fullSeries_near (-s) hd he _ _ _ _ A F) (fun a => ?_) hL hu
  refine lift_charge (f:=fun i s v => fullSeries A F (-s) hd he (x i).val (y i).val (basisWord a) v)
    (fun i s v => fullSeries_far (-s) hd he _ _ _ _ A F) (fun b => ?_) hL hv
  exact ChargeP.pull (full_charge_basis H law hK hx hS hy (indexScan a) (indexScan b) hd he
    (boundedByCaps a) (boundedByCaps b) p) (fun i => (x i,y i))

theorem uniform_tail_charge (p : ℕ) (hh : h ≤ l) (hL : 0 ≤ L) (hu : ∀ i, Box (u i) L)
    (hv : ∀ i, Box (v i) L) : ChargeP (p+1) ((h:ℝ)+1)
    (fun i s => tailSeries A F (-s) hd he hh (x i).val (y i).val (u i) (v i)) := by
  refine lift_charge (f:=fun i s u => tailSeries A F (-s) hd he hh (x i).val (y i).val u (v i))
    (fun i s u => tailSeries_near ..) (fun a => ?_) hL hu
  refine lift_charge (f:=fun i s v => tailSeries A F (-s) hd he hh (x i).val (y i).val (basisWord a) v)
    (fun i s v => tailSeries_far ..) (fun b => ?_) hL hv
  have ht := ChargeP.pull (ope_charge_basis H law hK hx hS hy (indexScan a) (indexScan b) hd he
    (boundedByCaps a) (boundedByCaps b) hh p) (fun i => (x i,y i))
  unfold tailSeries; simp_rw [ope_basis]; exact ht
end bounds
end YM.FVA2.GradedFar
