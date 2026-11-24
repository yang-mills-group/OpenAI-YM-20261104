import YM.GradedFar.Bound
import YM.GradedFar.Test
/-!
# The price inside a joint test

Through the finite terms at each target. The measure remains in its x,y coordinates
on their compacta. Thus no change of density to the Ty positions, and no Jacobians dropped.
-/
namespace YM.FVA2.GradedFar
noncomputable section
open Filter Function Real PowerSeries Set MeasureTheory
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe
open scoped Topology BigOperators Classical

variable {G : Gauge} {n m : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ} {N : WilsonPrescription G}
  {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
  {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple T A true)

private lemma cont_pull {I : Type} [TopologicalSpace I] (z : I → Points n)
    (h : Continuous z) (hz : ∀ i, z i ∈ conf n) {p : Points n → ℂ} (hp : ContinuousOn p (conf n)) :
    Continuous (fun i => p (z i)) := continuousOn_univ.mp (hp.comp h.continuousOn fun i _ => hz i)
private lemma cont_mul {I : Type} [TopologicalSpace I] (F : PowerSeries ℂ) (X : I → PowerSeries ℂ)
    (h : ∀ j, Continuous (fun i => coeff j (X i))) (j : ℕ) : Continuous (fun i => coeff j (F*X i)) := by
  simp_rw [coeff_mul]; exact continuous_finsetSum _ fun x _ => Continuous.const_mul (h _) _
private lemma cont_sum {I J : Type} [TopologicalSpace I] (s : Finset J) (F : J → I → PowerSeries ℂ)
    (hs : ∀ k j, Continuous (fun i => coeff j (F k i))) (j : ℕ) :
    Continuous (fun i => coeff j (∑ q ∈ s, F q i)) := by
  simp_rw [map_sum]; exact continuous_finsetSum _ fun x _ => hs x j
private lemma cont_crop {I : Type} [TopologicalSpace I] (F : I → PowerSeries ℂ) (t : ℝ)
    (hs : ∀ j, Continuous (fun i => coeff j (F i))) (j : ℕ) :
    Continuous (fun i => crop j t (F i)) := by
  simp only [crop_eq]; exact continuous_finsetSum _ fun x _ => Continuous.const_mul (hs _) _

include H
lemma cont_full {I : Type} [TopologicalSpace I] (x : I → Points n) (y : I → Points m)
    (hx : Continuous x) (hy : Continuous y) (s : ℝ)
    (h : ∀ i, forest (x i) (squeeze (-s) (y i)) ∈ conf (n+m))
    (u : Inputs G d) (v : Inputs G e) (k : ℕ) :
    Continuous (fun i => coeff k (Yx N T (x i) (y i) u v s)) := by
  refine cont_sum _ _ (fun a _ => cont_mul _ _ (fun _ => cont_sum _ _ (fun b _ => ?_) _) _) _
  refine cont_mul _ _ (fun j => cont_pull (fun i => forest (x i) (squeeze (-s) (y i)))
    (p:=fun z => coeff j (ordinary N _ z (Fin.append (roll a) (roll b))))
    (continual hx (hy.const_smul (exp (- -s)))) h ?_) _
  exact (H.separatedOPE (Teller.logNu 1)).wilson.awake _ _ _

lemma cont_center {I : Type} [TopologicalSpace I] (y : I → Points m)
    (hy : Continuous y) (s : ℝ) (h : ∀ i, outgoing (squeeze (-s) (y i)) ∈ conf (1+m))
    (v : Inputs G e) {l : ℕ} (q : Toon G l) (k : ℕ) :
    Continuous (fun i => coeff k (DX N T q (y i) v s)) := by
  refine cont_sum _ _ (fun b _ => cont_mul _ _ (fun j => cont_pull (p:=fun z => coeff j (ordinary N _ z (Fin.append (Single (flash q)) (roll b)))) _ ?_ h ?_) _) _
  · exact continual continuous_const (hy.const_smul (exp (- -s)))
  exact (H.separatedOPE (Teller.logNu 1)).wilson.awake _ _ _

lemma cont_series {I : Type} [TopologicalSpace I] (x : I → Points n)
    (hx : Continuous x) (h : ∀ i, x i ∈ conf n)
    (u : Inputs G d) (q : Q G) (k : ℕ) : Continuous (fun i => coeff k (seriesComponent N (x i) u q)) := by
  refine cont_sum _ _ (fun a j => cont_mul _ _ (fun k => cont_pull (p:=fun y => coeff k (FarCoefficients (book N) (roll a) y q)) _ hx h ?_) _) _
  exact ((H.separatedOPE (Teller.logNu 1)).wilson.far _).2.1 q _

variable {K : Set (Points n)} {S : Set (Points m)}
  (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ O.Enh.Outside m)
  (d e) (L R : ℝ) (p h : ℕ)
include hK hx hS hy

-- The real binder r in this theorem is the *physical stretch T*.
/-- In particular works with arbitrary finite-(total-variation) signed **joint** tests (
E the reals, B the flipping of the scalar multiplication into ℂ). For complex tests, use E=`ℂ`
and take B to be complex multiplication (over `ℝ`). Those cases have `‖B‖=1`. We state the
result with T₀ independent even of the test.
-/
theorem tested : ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∃ T₀ : ℝ, 2 ≤ T₀ ∧
    ∀ r ≥ T₀, ∀ u : Inputs G d, Within L u → ∀ v : Inputs G e, Within R v →
    ∀ t g : ℝ, |t| ≤ 1 → |t| ≤ 2*g →
    let P := fun i : ↥K × ↥S => crop p t (Yx N T i.1.val i.2.val u v (log r))
    let Q := fun i : ↥K × ↥S => crop p t (Dx N T i.2.val v (log r) (cActual N i.1.val u h p t))
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E],
     ∀ (φ : VectorMeasure (↥K × ↥S) E) [IsFiniteMeasure φ.variation] (B : ℂ →L[ℝ] E →L[ℝ] ℂ),
      φ.Integrable P ∧ φ.Integrable Q ∧
      ‖(∫ᵛ x, P x ∂[B; φ]) - (∫ᵛ x, Q x ∂[B; φ])‖ ≤
        C * (r⁻¹^(h+1) + g^(p+1)) * (1+log r)^a * ‖B‖ * φ.variation.real univ := by
  obtain ⟨C,hC,a,T0,h0,hr⟩ := prices H hK hx hS hy d e L R p h
  refine ⟨C,hC,a,T0,h0,?_⟩
  intro r hr' u pu v pv t g ht hg P Q E _ _ φ _ B
  letI := isCompact_iff_compactSpace.mp hK; letI := isCompact_iff_compactSpace.mp hS
  let x (i : ↥K × ↥S) := i.1.val; let y (i : ↥K × ↥S) := i.2.val
  have cx : Continuous x := continuous_subtype_val.comp continuous_fst
  have cy : Continuous y := continuous_subtype_val.comp continuous_snd
  have hp (i) := hr r hr' (x i) i.1.property (y i) i.2.property
  have hr0 : 0 < r := by linarith
  have hsq (i) : squeeze (-log r) (y i) = r • y i := squeeze_far (y i) hr0
  have ct (j : Toon G h) k : Continuous (fun i => coeff k (DX N T j (y i) v (log r))) := cont_center H y cy
    (log r) (fun i => by rw [hsq]; exact (hp i).1.2) v j k
  have ct' (j : Toon G h) k : Continuous (fun i => coeff k (seriesComponent N (x i) u (flash j))) :=
    cont_series H x cx (fun i => hx i.1.property) u _ k
  refine pair_integral φ B ?_ ?_ _ fun i => (hp i).2 u pu v pv t g ht hg
  · exact cont_crop _ _ (cont_full H x y cx cy _ (fun i => by rw [hsq]; exact (hp i).1.1) u v) _
  unfold Q; simp_rw [charged_identity]
  exact continuous_finsetSum _ fun q _ => (cont_crop _ t (ct' q) p).mul (cont_crop _ t (ct q) p)
-- no moving densities
end
end YM.FVA2.GradedFar
