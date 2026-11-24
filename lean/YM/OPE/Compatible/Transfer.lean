import YM.OPE.Compatible.OrbitCost

/-!
# Rate bounds from signed exterior comparisons
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cov
open Function Set Filter Table Survey MeasureTheory
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {L:Register G} {S:Table L} {P : DiffPlan S} {R : S.Rotation} {ρ : S.RealSpin}
  {B l:Type} [Fintype B] {φ : Filter l} {T : l → ℝ} {κ : ℝ} {d : ℕ}

lemma integrates_price {X:Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Q : l → Ortho → X)
    (h : ∀ K : l → Ortho, RateLE φ T (fun i => Q i (K i)) κ) :
    RateLE φ T (fun i => ∫ g,Q i g ∂angles) κ := by
  intro a ha
  filter_upwards [universalize (p:=fun i g => ‖Q i g‖ ≤ Real.exp (a*T i)) (fun k => h k a ha)] with i hi
  exact (norm_integral_le_of_norm_le (integrable_const (Real.exp (a*T i))) (Eventually.of_forall hi)).trans (by simp)

variable (J : B → Type) [∀ b, Fintype (J b)]
  (O : l → E4) (X : (b:B) → l → J b → E4) (v : (b:B) → l → J b → S.Tag)
  (c : B → l → ℂ)
variable (hT : Tendsto T φ atTop) (H : Fits J O X φ) (hw : NearProbes J O X v c φ T κ)
  (hR : R.Laws P ρ) (hs : S.Hierarchy)
include hT H hw hR hs
lemma packed_raw (D : Prism (S:=S) (d:=d)) : RateLE φ T (fun i =>
    ∑ b, c b i • Survey.raw R D (away (X b i) (O i)) (v b i)) κ := by
  let F (i:l) (K:Ortho) := ∑ b,c b i • shot R D (away (X b i) (O i)) (v b i) K
  have hf := integrates_price F (fun K => packed_shot J O X v c hT H hw D hR hs K)
  apply hf.congr
  filter_upwards [eventually_all.mpr fun b => Fits.sized J O X H D b] with i hi
  have hj (b:B) : Integrable (fun K => c b i • shot R D (away (X b i) (O i)) (v b i) K) angles :=
    (shot_integrable D hR hs.smooth (v b i) (hi b)).smul (c b i)
  apply Eq.trans (integral_finsetSum _ (fun b _ => hj b))
  refine Finset.sum_congr rfl fun b _ => integral_smul ..

omit hR hT in
lemma conjugate_price (ρ : S.RealSpin) : NearProbes J O X (fun b i => conjugate ρ ∘ v b i)
    (fun b i => star (c b i)) φ T κ := by
  constructor
  intro I _ w y δ hδ he
  refine (hw.fare (conjugate ρ ∘ w) y hδ he).transfer ?_
  filter_upwards [eventually_all.mpr fun b => Fits.separated J O X H b y hδ he] with i hi
  have hh (b:B) := kernel_conj hs.laws.toSymmetric ρ ρ
    (show S.respects S from fun _ => le_rfl) (beside (v b i) (conjugate ρ ∘ w)) (hi b)
  simp_rw [beside_commutes, show conjugate ρ ∘ conjugate ρ ∘ w = w from funext fun i => conjugate_twice ρ _] at hh
  simp_rw [hh, ← star_mul', ← star_sum]; rw [norm_star]

lemma packed_projection (D : Prism (S:=S) (d:=d)) : RateLE φ T (fun i =>
    ∑ b, c b i • projection R D ρ (away (X b i) (O i)) (v b i)) κ := by
  have he := (packed_raw J O X v c hT H hw hR hs D).add ((packed_raw J O X _ _ hT H
    (conjugate_price J O X v c H hw hs ρ) hR hs D).linear hT (reflectionC ρ d)) hT
  refine (((RateLE.const ((2:ℂ)⁻¹) hT).smul he).mono (zero_add _ |>.le)).congr
    (Eventually.of_forall fun i => ?_)
  change (2:ℂ)⁻¹ • ((∑ b, c b i • _) + S.conj ρ d (∑ b, star (c b i) • _)) = _
  simp_rw [map_sum,map_smulₛₗ]; simp only [starRingEnd_apply, star_star, projection]
  rw [← Finset.sum_add_distrib,Finset.smul_sum]; exact Finset.sum_congr rfl fun b _ => (by
    rw [smul_comm (c b i),smul_add (c b i)])

/-- Any finite tower readout is then priced. No relative error assumption,
no estimates required on the point coefficients of the signed combination,
just know the *whole* fit. -/
lemma absorb (D : Sheets S) (d : ℕ) : RateLE φ T (fun i =>
    ∑ b, c b i • ascend D P R ρ d (away (X b i) (O i)) (v b i)) κ := by
  induction d with
  | zero => simpa only [ascend] using packed_projection J O X v c hT H hw hR hs (D 0)
  | succ d ih =>
    have hp := packed_projection J O X v c hT H hw hR hs (D (d+1))
    obtain ⟨r,hr⟩ := one_lin D hR hs d
    let F := LinearMap.toContinuousLinearMap (r.restrictScalars ℝ)
    let W := P.rise (Nat.le_succ d)
    refine (hp.add ((ih.sub (hp.linear hT F) hT).linear hT
      (LinearMap.toContinuousLinearMap (W.restrictScalars ℝ))) hT).congr
      (Eventually.of_forall fun i => ?_)
    let k := fun b => projection R (D (d+1)) ρ (away (X b i) (O i)) (v b i)
    let v' := fun b => ascend D P R ρ d (away (X b i) (O i)) (v b i)
    simp_rw [ascend.eq_2] -- eq lemma?
    change (∑ b, c b i • k b) + W ((∑ b,c b i • v' b) - r (∑ b,c b i • k b)) = _
    rw [map_sum r,← Finset.sum_sub_distrib,map_sum W,← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, ← smul_sub,map_smul,hr,← smul_add]
end YM.OPE.Cov
