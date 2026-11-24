import YM.OPE.Compatible.Units

/-!
# Rate bounds from a finite exterior demand

When combining two-scale rates this finite-demand version matters: need to
know the *finite* collection of capacities prior to choosing sufficient
intermediate horizons. The proof is the same transfer on the actual compact
motion projection as in OrbitCost and Transfer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cov
open Function Set Filter Table Survey MeasureTheory
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {L:Register G} {S:Table L} {P : DiffPlan S} {R : S.Rotation} {ρ : S.RealSpin}
  {B l:Type} [Fintype B] {φ : Filter l} {T : l → ℝ} {κ : ℝ} {d : ℕ}


def wrist (D : Prism (S:=S) (d:=d)) := Finset.univ.sup (fun e:D.probes => Display.bill (S.classTokens ∘ e.val.letter))
lemma wrist_ge (D : Prism (S:=S) (d:=d)) (e:D.probes) : Display.bill (S.classTokens ∘ e.val.letter) ≤ wrist D :=
  Finset.le_sup (s:=Finset.univ) (f:=fun e:D.probes => Display.bill (S.classTokens ∘ e.val.letter))
    (Finset.mem_univ e)

def palm (D : Sheets S) (d : ℕ) := (Finset.range (d+1)).sup (fun k => wrist (D k))
lemma palm_ge (D : Sheets S) {k d:ℕ} (h:k≤d) : wrist (D k) ≤ palm D d :=
  Finset.le_sup (s:=Finset.range (d+1)) (f:=fun k => wrist (D k)) (b:=k)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
lemma palm_order (D:Sheets S) : Monotone (palm D) := fun _ _ h =>
  Finset.sup_le (fun _ hb => palm_ge D (le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hb)) h))

variable (J : B → Type) [∀ b, Fintype (J b)]
  (O : l → E4) (X : (b:B) → l → J b → E4) (v : (b:B) → l → J b → S.Tag)
  (c : B → l → ℂ)
/-- Price with whole signed cancellation, at fixed exterior clearance. -/
structure FiniteEyes (φ : Filter l) (T : l → ℝ) (u : ℝ) (cap : ℕ) : Prop where
  fare {I : Type} [Fintype I] (w : I → S.Tag) (y : l → I → E4) {δ : ℝ} :
    Display.bill w ≤ cap → 0 < δ → (∀ᶠ i in φ, ClearOf (O i) (y i) δ) → RateLE φ T (fun i =>
      ∑ b, c b i * kernel S (beside (X b i) (y i)) (beside (v b i) w)) u

variable (hT : Tendsto T φ atTop) (H : Fits J O X φ) {cap:ℕ} (hw : FiniteEyes J O X v c φ T κ cap)
  (hR : R.Laws P ρ) (hs : S.Hierarchy)
include hT H hw hR hs
lemma withEyes (D : Prism (S:=S) (d:=d)) (hD : wrist D ≤ cap) (K : l → Ortho) : RateLE φ T (fun i =>
    ∑ b, c b i • shot R D (away (X b i) (O i)) (v b i) (K i)) κ := by
  let Y (i:l) (e:D.probes) := placements e.val (K i)
  let g (i:l) (e:D.probes) := ∑ b:B,c b i *
    kernel S (beside (away (X b i) (O i)) (Y i e)) (beside (v b i) (labelSet R e.val (K i)))
  have he (e:D.probes) : RateLE φ T (fun i=>g i e) κ := by
    let n (j:Fin e.val.n) := (e.val.letter j).fst
    let M (i:l) : MultilinearMap ℂ (fun j => S.Field (n j)) ℂ :=
      ∑ b,c b i • withExterior S (away (X b i) (O i)) (v b i) n (Y i e)
    have hj (i:l) (w : Slots S n) : M i w = ∑ b:B, c b i *
      kernel S (beside (away (X b i) (O i)) (Y i e)) (beside (v b i) (stockTag w)) := by
        unfold M; simp_rw [sum_apply, smul_apply,exterior_apply]; rfl
    have hh (w : Slots S n) : RateLE φ T (fun i => M i w) κ := by
      obtain ⟨δ,hδ,hc⟩ := RateLocations e.val K O
      apply (hw.fare (stockTag w) (fun i j => Y i e j + O i) ((wrist_ge D e).trans hD) hδ (Eventually.of_forall hc)).congr
      filter_upwards [eventually_all.mpr fun b => Fits.sized J O X H D b] with i hi
      rw [hj]
      refine Finset.sum_congr rfl fun b _ => congr_arg (c b i * ·) ?_
      have hh := kernel_shift hs.translations (beside (v b i) (stockTag w))
        (lives D (hi b) e (K i)) (O i)
      rwa [show (fun j => beside (away (X b i) (O i)) (placements e.val (K i)) j + O i) =
        beside (X b i) (fun j => Y i e j + O i) from funext fun j => by
          rcases j with j|j
          · simp [away]
          rfl] at hh
    let x (A : Ortho) : Slots S n := fun i => (labelSet R e.val A i).2
    have he := multilinear_price M hT x (continuous_pi (f:=x) fun i => hR.spin (n i)
        (S.classTokens (e.val.letter i)).2) K hh
    exact he.congr (Eventually.of_forall fun i => hj i (x (K i)))
  have hg : RateLE φ T g κ := by
    intro a ha
    filter_upwards [eventually_all.mpr fun j : D.probes => he j a ha] with i hi
    exact (pi_norm_le_iff_of_nonneg (Real.exp_nonneg _)).mpr hi
  let F := LinearMap.toContinuousLinearMap (D.decode.restrictScalars ℝ)
  let E := fun (K:Ortho) => LinearMap.toContinuousLinearMap (((R.act d K).toLinearMap).restrictScalars ℝ)
  have hec : Continuous E := linear_orbit R hR d
  have hen : Continuous (fun i => ‖E i‖) := (show Continuous (fun A : S.Field d →L[ℝ] S.Field d => ‖A‖) from continuous_norm (E:=S.Field d →L[ℝ] S.Field d)).comp hec
  obtain ⟨C,hC⟩ := (isCompact_range hen).bddAbove
  have h' := (RateLE.absBound (F:=E ∘ K) C hT (Eventually.of_forall fun i => hC (mem_range_self (K i))))
  refine ((h'.bil (u:=fun i => E (K i) (F (g i))) (hg.linear hT F) (Eventually.of_forall fun i =>
    (E (K i)).le_opNorm _)).mono (zero_add κ |>.le)).congr (Eventually.of_forall fun i => ?_)
  change R.act _ _ (D.decode (g i)) = _
  have hv : g i = ∑ b, c b i • (fun e:D.probes =>
        kernel S (beside (away (X b i) (O i)) (Y i e)) (beside (v b i) (labelSet R e.val (K i)))) := by
    ext1 e; unfold g; simp only [Finset.sum_apply]; rfl
  rw [hv,map_sum,map_sum]; simp_rw [map_smul]; rfl
lemma withEyes_raw (D : Prism (S:=S) (d:=d)) (hD : wrist D ≤ cap) : RateLE φ T (fun i =>
    ∑ b, c b i • Survey.raw R D (away (X b i) (O i)) (v b i)) κ := by
  let F (i:l) (K:Ortho) := ∑ b,c b i • shot R D (away (X b i) (O i)) (v b i) K
  have hf := integrates_price F (fun K => withEyes J O X v c hT H hw hR hs D hD K)
  apply hf.congr
  filter_upwards [eventually_all.mpr fun b => Fits.sized J O X H D b] with i hi
  have hj (b:B) : Integrable (fun K => c b i • shot R D (away (X b i) (O i)) (v b i) K) angles :=
    (shot_integrable D hR hs.smooth (v b i) (hi b)).smul (c b i)
  apply Eq.trans (integral_finsetSum _ (fun b _ => hj b))
  refine Finset.sum_congr rfl fun b _ => integral_smul ..

omit hR hT in
lemma conj_finite (ρ : S.RealSpin) : FiniteEyes J O X (fun b i => conjugate ρ ∘ v b i)
    (fun b i => star (c b i)) φ T κ cap := by
  constructor
  intro I _ w y δ ht hδ he
  refine (hw.fare (conjugate ρ ∘ w) y ht hδ he).transfer ?_
  filter_upwards [eventually_all.mpr fun b => Fits.separated J O X H b y hδ he] with i hi
  have hh (b:B) := kernel_conj hs.laws.toSymmetric ρ ρ
    (show S.respects S from fun _ => le_rfl) (beside (v b i) (conjugate ρ ∘ w)) (hi b)
  simp_rw [beside_commutes, show conjugate ρ ∘ conjugate ρ ∘ w = w from funext fun i => conjugate_twice ρ _] at hh
  simp_rw [hh, ← star_mul', ← star_sum]; rw [norm_star]

lemma finiteEyes_projection (D : Prism (S:=S) (d:=d)) (hD : wrist D ≤ cap) : RateLE φ T (fun i =>
    ∑ b, c b i • projection R D ρ (away (X b i) (O i)) (v b i)) κ := by
  have he := (withEyes_raw J O X v c hT H hw hR hs D hD).add ((withEyes_raw J O X _ _ hT H
    (conj_finite J O X v c H hw hs ρ) hR hs D hD).linear hT (reflectionC ρ d)) hT
  refine (((RateLE.const ((2:ℂ)⁻¹) hT).smul he).mono (zero_add _ |>.le)).congr
    (Eventually.of_forall fun i => ?_)
  change (2:ℂ)⁻¹ • ((∑ b, c b i • _) + S.conj ρ d (∑ b, star (c b i) • _)) = _
  simp_rw [map_sum,map_smulₛₗ]; simp only [starRingEnd_apply, star_star, projection]
  rw [← Finset.sum_add_distrib,Finset.smul_sum]; exact Finset.sum_congr rfl fun b _ => (by
    rw [smul_comm (c b i),smul_add (c b i)])

/-- Any finite tower readout is then priced. No relative error assumption,
no estimates required on the point coefficients of the signed combination,
just know the *whole* fit. -/
lemma finiteEyes_absorb (D : Sheets S) (d : ℕ) (hD:palm D d ≤ cap) : RateLE φ T (fun i =>
    ∑ b, c b i • ascend D P R ρ d (away (X b i) (O i)) (v b i)) κ := by
  induction d with
  | zero => simpa only [ascend] using finiteEyes_projection J O X v c hT H hw hR hs (D 0) ((palm_ge D le_rfl).trans hD)
  | succ d ih =>
    have hp := finiteEyes_projection J O X v c hT H hw hR hs (D (d+1)) ((palm_ge D le_rfl).trans hD)
    obtain ⟨r,hr⟩ := one_lin D hR hs d
    let F := LinearMap.toContinuousLinearMap (r.restrictScalars ℝ)
    let W := P.rise (Nat.le_succ d)
    refine (hp.add (((ih (((palm_order D) (Nat.le_succ d)).trans hD)).sub (hp.linear hT F) hT).linear hT
      (LinearMap.toContinuousLinearMap (W.restrictScalars ℝ))) hT).congr
      (Eventually.of_forall fun i => ?_)
    let k := fun b => projection R (D (d+1)) ρ (away (X b i) (O i)) (v b i)
    let v' := fun b => ascend D P R ρ d (away (X b i) (O i)) (v b i)
    simp_rw [ascend.eq_2]
    change (∑ b, c b i • k b) + W ((∑ b,c b i • v' b) - r (∑ b,c b i • k b)) = _
    rw [map_sum r,← Finset.sum_sub_distrib,map_sum W,← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, ← smul_sub,map_smul,hr,← smul_add]
end YM.OPE.Cov

namespace YM.OPE.Cov.Display
open Function Set Filter MeasureTheory
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book} (U:Spec.Final C f S)
variable {I J B l:Type} [FI : Fintype I] [FJ : Fintype J] [Fintype B] {φ : Filter l} {T : l → ℝ} {κ : ℝ}

-- arity I compared with a finite sum of words of arity J, can also take B empty
lemma finiteEye_exchange (k : ℕ) (O : l → E4) (X : l → I → E4) (Y : B → l → J → E4)
    (p : l → I → S.Tag) (q : B → l → J → S.Tag) (a : B → l → ℂ)
    (hT : Tendsto T φ atTop)
    (hx : Tendsto (fun i => away (X i) (O i)) φ (𝓝 0))
    (hx' : ∀ᶠ i in φ, Injective (X i))
    (hy : ∀ b, Tendsto (fun i => away (Y b i) (O i)) φ (𝓝 0))
    (hy' : ∀ b, ∀ᶠ i in φ, Injective (Y b i))
    (h : ∀ (K:Type) [Fintype K] (w : K → S.Tag) (y : l → K → E4) {δ : ℝ},
      bill w ≤ palm (supplies S) k → 0 < δ → (∀ᶠ i in φ, ClearOf (O i) (y i) δ) → RateLE φ T (fun i =>
        kernel S (beside (X i) (y i)) (beside (p i) w) - ∑ b, a b i *
          kernel S (beside (Y b i) (y i)) (beside (q b i) w)) κ) :
    RateLE φ T (fun i => ray U k (X i) (p i) (O i) -
        ∑ b, a b i • ray U k (Y b i) (q b i) (O i)) κ := by
  let N : Unit⊕B → Type := Sum.elim (fun _ => I) (fun _ => J)
  let z : (b : Unit⊕B) → l → N b → E4 := Sum.rec (fun _ => X) Y
  let v : (b : Unit⊕B) → l → N b → S.Tag := Sum.rec (fun _ => p) q
  let c : Unit⊕B → l → ℂ := Sum.elim (fun _ _ => 1) (fun b i => - a b i)
  letI NF : ∀ b, Fintype (N b) := Sum.rec (fun _ => FI)
    (fun _ => FJ)
  have he : Fits N O z φ := by
    constructor
    · rintro (t|t)
      exact hx
      exact hy t
    rintro (t|t)
    exact hx'
    exact hy' t
  have hu : FiniteEyes N O z v c φ T κ (palm (supplies S) k) := by
    constructor; intro k hk w y δ hw hδ hh; apply (h k w y hw hδ hh).congr
    apply Eventually.of_forall
    intro i; dsimp only; rw [Fintype.sum_sum_type]; conv_rhs => rw [Fintype.sum_unique]
    change _ - _ = 1 * _ + ∑ b:B, (-a b i)* kernel S (beside (Y b i) (y i)) (beside (q b i) w)
    rw [one_mul]; simp_rw [neg_mul,Finset.sum_neg_distrib,sub_eq_add_neg]; rfl
  refine (finiteEyes_absorb N O z v c hT he hu U.phase.transport.spots U.room.kernel (supplies S) k le_rfl).congr
    (Eventually.of_forall fun i => ?_)
  dsimp only; rw [Fintype.sum_sum_type,Fintype.sum_unique]
  change ((1:ℂ) • (ray U k (X i) (p i) (O i)) + ∑ b, (-a b i) • ray U k (Y b i) (q b i) (O i)) = _
  simp [sub_eq_add_neg]
end YM.OPE.Cov.Display
