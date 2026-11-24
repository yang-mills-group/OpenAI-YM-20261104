import YM.OPE.Compatible.Lux.Harp
/-! Rates to power-budget. Transfer signed, choose polynomial after fixed horizon. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Set Filter MeasureTheory
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G:Gauge} {L:Register G} {S:Table L} {l J:Type} [Fintype J]
  {φ : Filter l} {T : l → ℝ} 
namespace Cov
lemma multi_score {b : J → ℕ} (M : l → MultilinearMap ℂ (fun j : J => S.Field (b j)) ℂ)
    (hT : Tendsto T φ atTop) (x : Ortho → Slots S b) (hc : Continuous x) (K : l → Ortho)
    (he : ∀ v, Score φ T (fun i => M i v)) : Score φ T (fun i => M i (x (K i))) := by
  let f := fun j:J => Module.finBasis ℂ (S.Field (b j))
  have hq (a : ∀ j, Fin (Module.finrank ℂ (S.Field (b j)))) : Continuous (fun g:Ortho =>
      (∏ i, (f i).coord (a i) (x g i))) := continuous_finsetProd _ fun i _ =>
        ((f i).coord (a i)).continuous_of_finiteDimensional.comp ((continuous_pi_iff.mp hc) i)
  conv => arg 3; ext i; rw [decompose]
  apply Score.summar _ _ hT; intro a _
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hq a).continuousOn
  let v : Slots S b := fun i => f i (a i)
  exact ((Score.bound (p:=fun k:l => ∏ i, (f i).coord (a i) (x (K k) i)) C hT
    (Eventually.of_forall fun k => hC _ (mem_univ (K k)))).product (he v))

-- Price signed combinations. Positions in absolute coordinates about `O i`.
section Pack
variable {B:Type} [Fintype B] (J : B → Type) [∀ b, Fintype (J b)]
  (O : l → E4) (X : (b:B) → l → J b → E4) (v : (b:B) → l → J b → S.Tag)
  (c : B → l → ℂ)

/-- Price with whole signed cancellation, at fixed exterior clearance. -/
structure SharpProbes (φ : Filter l) (T : l → ℝ) : Prop where
  fare {I : Type} [Fintype I] (w : I → S.Tag) (y : l → I → E4) {δ : ℝ} :
    0 < δ → (∀ᶠ i in φ, ClearOf (O i) (y i) δ) → Score φ T (fun i =>
      ∑ b, c b i * kernel S (beside (X b i) (y i)) (beside (v b i) w))

variable (hT : Tendsto T φ atTop)
variable (H : Fits J O X φ) (hw : SharpProbes J O X v c φ T)
variable {d : ℕ} (D : Prism (S:=S) (d:=d)) -- d implicit edit
open Table Survey
variable {P : DiffPlan S} {R : S.Rotation} {ρ : S.RealSpin} (hR : R.Laws P ρ) (hs : S.Hierarchy)
include H hw hT hR hs
lemma angled_score (K : l → Ortho) : Score φ T (fun i =>
    ∑ b, c b i • shot R D (away (X b i) (O i)) (v b i) (K i)) := by
  let Y (i:l) (e:D.probes) := placements e.val (K i)
  let g (i:l) (e:D.probes) := ∑ b:B,c b i *
    kernel S (beside (away (X b i) (O i)) (Y i e)) (beside (v b i) (labelSet R e.val (K i)))
  have he (e:D.probes) : Score φ T (fun i=>g i e) := by
    let n (j:Fin e.val.n) := (e.val.letter j).fst
    let M (i:l) : MultilinearMap ℂ (fun j => S.Field (n j)) ℂ :=
      ∑ b,c b i • withExterior S (away (X b i) (O i)) (v b i) n (Y i e)
    have hj (i:l) (w : Slots S n) : M i w = ∑ b:B, c b i *
      kernel S (beside (away (X b i) (O i)) (Y i e)) (beside (v b i) (stockTag w)) := by
        unfold M; simp_rw [sum_apply, smul_apply,exterior_apply]; rfl
    have hh (w : Slots S n) : Score φ T (fun i => M i w) := by
      obtain ⟨δ,hδ,hc⟩ := RateLocations e.val K O
      apply (hw.fare (stockTag w) (fun i j => Y i e j + O i) hδ (Eventually.of_forall hc)).congr
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
    have he := multi_score M hT x (continuous_pi (f:=x) fun i => hR.spin (n i)
        (S.classTokens (e.val.letter i)).2) K hh
    exact he.congr (Eventually.of_forall fun i => hj i (x (K i)))
  have hg : Score φ T g := Score.allPi hT he
  let F := LinearMap.toContinuousLinearMap (D.decode.restrictScalars ℝ)
  let E := fun (K:Ortho) => LinearMap.toContinuousLinearMap (((R.act d K).toLinearMap).restrictScalars ℝ)
  have hec : Continuous E := linear_orbit R hR d
  have hen : Continuous (fun i => ‖E i‖) := (show Continuous (fun A : S.Field d →L[ℝ] S.Field d => ‖A‖) from continuous_norm (E:=S.Field d →L[ℝ] S.Field d)).comp hec
  obtain ⟨C,hC⟩ := (isCompact_range hen).bddAbove
  have h' := (Score.bound (p:=E ∘ K) C hT (Eventually.of_forall fun i => hC (mem_range_self (K i))))
  refine ((Score.utility (f:=E ∘ K) h' (w:=fun i => E (K i) (F (g i))) (hg.lift_l hT F) (Eventually.of_forall fun i =>
    (E (K i)).le_opNorm _))).congr (Eventually.of_forall fun i => ?_)
  change R.act _ _ (D.decode (g i)) = _
  have hv : g i = ∑ b, c b i • (fun e:D.probes =>
        kernel S (beside (away (X b i) (O i)) (Y i e)) (beside (v b i) (labelSet R e.val (K i)))) := by
    ext1 e; unfold g; simp only [Finset.sum_apply]; rfl
  rw [hv,map_sum,map_sum]; simp_rw [map_smul]; rfl
end Pack
end Cov
end YM.OPE
