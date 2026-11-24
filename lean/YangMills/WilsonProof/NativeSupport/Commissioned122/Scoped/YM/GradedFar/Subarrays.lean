import YangMills.WilsonProof.NativeSupport.Commissioned122.Scoped.YM.GradedFar.Padding
import YangMills.WilsonProof.NativeSupport.Commissioned122.Scoped.YM.GradedFar.Prices

/-!
# Subtuple use

The estimates include every deletion too, with *its* prescribed FarCoefficients.
Use them at the sublayout with unchanged Far/positions for that subproblem. For
paying the calls themselves on those layouts, these identities also allow just
using the units in the parent layouts. Note positive clearance assumptions are
never made at a coincidence and we don't extend by contact terms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Function Set Scale O.Score O.Enh O.Read O.Canon PowerSeries Dframe
open XSpace XSpace.Normalize MS.Land
open scoped Classical BigOperators

variable {G : Gauge} (N : Register.WilsonPrescription G)
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {Sms : MS.Land.Prescription (Press.portDeck G)}
    {hG : G.Simple} (matched : Main.Match N hG M Sms true)
    {n m a b h k H : ℕ} (A : Fin a ↪ Fin n) (C : Fin b ↪ Fin m)
    {d : Fin n → ℕ} {e : Fin m → ℕ}

def subarray : Fin (a+b) ↪ Fin (n+m) := (Equiv.toEmbedding finSumFinEquiv.symm).trans
  ((Function.Embedding.sumMap A C).trans (Equiv.toEmbedding finSumFinEquiv))
lemma sub_left (i : Fin a) : subarray A C (Fin.castAdd b i) = Fin.castAdd m (A i) := by simp [subarray]
lemma sub_right (i : Fin b) : subarray A C (Fin.natAdd a i) = Fin.natAdd n (C i) := by simp [subarray]

lemma projected (x : Points n) (y : Points m) : positions (subarray A C) (forest x y) =
    forest (positions A x) (positions C y) := by
  ext1 i; induction i using Fin.addCases <;> simp [positions_val, sub_left, sub_right]
lemma projected_scale (T : ℝ) (y : Points m) : positions C (T • y) = T • positions C y := by
  ext1 i; rfl
lemma projected_outside {y : Points m} (hy : y ∈ Outside m) : positions C y ∈ Outside b := by
  change forest (0:Points 1) (positions C y) ∈ conf _
  simpa only [projected, show positions (Function.Embedding.refl (Fin 1)) (0:Points 1)=
    (0:Points 1) from rfl] using positions_conf (subarray (Function.Embedding.refl (Fin 1)) C) hy

/-- Sets of subconfigurations are eligible shapes without paying new shrinking clearances. -/
theorem compact_subgeometry {K : Set (Points n)} {S : Set (Points m)}
    (kc : IsCompact K) (hk : K ⊆ conf n) (sc : IsCompact S) (hs : S ⊆ Outside m) :
    IsCompact (positions A '' K) ∧ (positions A '' K) ⊆ conf a ∧
    IsCompact (positions C '' S) ∧ (positions C '' S) ⊆ Outside b :=
  ⟨kc.image (positions_cont A), image_subset_iff.mpr (fun _ hx => positions_conf A (hk hx)),
    sc.image (positions_cont C), image_subset_iff.mpr (fun _ hx => projected_outside C (hs hx))⟩

lemma within_abbr (d : Fin n → ℕ) (hd : Covered d H) : Covered (d ∘ A) H := fun i => hd (A i)

local notation "V'" => Scale.Measure.outlook N.scheme N.criterion
local notation "B" => GroupS.gaugeN N.scheme N.criterion M

include matched
theorem series_select (ν : ℝ) (z : Points (n+m)) (hz : z ∈ conf _) (η : ℝ)
    (hd : Covered d H) (he : Covered e H) (u : Appointed122Fields G d)
    (hu : ∀ i : Fin n, i∉Set.range A → u i = leaf G (d i))
    (v : Appointed122Fields G e) (hv : ∀ i : Fin m, i∉Set.range C → v i = leaf G (e i)) :
    series V' (B ν) η z hd he u v =
    series V' (B ν) η (positions (subarray A C) z) (within_abbr A d hd) (within_abbr C e he)
      (fun i => u (A i)) (fun i => v (C i)) := by
  ext1 k
  have hV d := (matched.dilation ν).check.paid η d
  simp only [series_coeff, ordered_apply, extAt_at V' hz, extAt_at V' (positions_conf (subarray A C) hz)]
  rw [sum_padded C _ k]; swap
  · intro j _ i hi ht; apply MultilinearMap.map_coord_zero (i:=Fin.natAdd n i);
    rw [Fin.append_right,hv i hi,transfer_unit _ η (hV _),if_neg ht,map_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  let v' := Fin.append (fun i => up (hd i) (u i))
    (fun j => up (he j) (coeff (pad C i (some j)) (transfer (B ν) η (e j)) (v j)))
  have h : Padded (subarray A C) v' := by
    intro j; induction j using Fin.addCases with
    | left j =>
      intro hj; have he : j∉Set.range A := by
        rintro ⟨j,rfl⟩; exact hj ⟨Fin.castAdd b j, sub_left A C j⟩
      rw [show v' (Fin.castAdd m j)= _ from Fin.append_left .., hu j he]; rfl
    | right j =>
      intro hj; have hr : j∉Set.range C := by
        rintro ⟨j,rfl⟩; exact hj ⟨Fin.natAdd a j, sub_right A C j⟩
      rw [show v' (Fin.natAdd n j)= _ from Fin.append_right .., hv j hr, transfer_unit _ η (hV _),
        pad_off C _ hr, if_pos rfl]; rfl
  rw [pad_none, outlook_padded (subarray A C) N matched (i none) ⟨z,hz⟩ v' h]
  apply congr_arg; funext j; induction j using Fin.addCases <;>
    simp only [Function.comp_apply,v', sub_left,sub_right,Fin.append_left,Fin.append_right,pad_some] <;> rfl

theorem series_empty (ν : ℝ) (z : Points (0+0)) (η : ℝ)
    {d e : Fin 0 → ℕ} (hd : Covered d H) (he : Covered e H) (u : Appointed122Fields G d) (v : Appointed122Fields G e) :
    series V' (B ν) η z hd he u v = 1 := by
  ext k; rw [series_coeff,ordered_apply,blank_tally, Finset.sum_singleton,Finsupp.single_eq_same]
  have h : z ∈ conf _ := fun i j h => Fin.elim0 (show Fin 0 from i)
  rw [extAt_at V' h]; exact paddingOutlookEmpty122 N matched k _ _
end YM.FVA2.GradedFar

