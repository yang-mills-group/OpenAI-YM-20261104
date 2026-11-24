import YM.Integration.WilsonLocalPlaquetteMultiplicity

/-! A price in terms of the changed bonds themselves. Each of the four
actual angular entries is charged at its own size, before any choice of
connected support, torus, finite forest, or cutoff. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalPlaquetteBonds
open Finset Lattice Wilson RG WilsonPlaquetteIncidence
open WilsonLocalPlaquetteTaylor WilsonLocalPlaquetteField WilsonLocalPlaquetteAction
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {n:Side}

theorem maximum (u:Angles G) (k:ℕ) : ‖u‖^k≤∑j:Fin 4,‖u j‖^k := by
  obtain ⟨j,hj,high⟩:=univ.exists_max_image (fun j:Fin 4=>‖u j‖) univ_nonempty
  have cap : ‖u‖≤‖u j‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun l=>high l (mem_univ _))
  exact (pow_le_pow_left₀ (norm_nonneg u) cap k).trans (single_le_sum (fun l _=>pow_nonneg (norm_nonneg (u l)) k) hj)

theorem original (k:ℕ) (S:Finset (Bonds n)) (X Y:Angular G n) :
    load (k+1) S X Y ≤6*∑e∈S,(‖X e‖^(k+1)+‖Y e‖^(k+1)) := by
  let h (e:Bonds n):=if e∈S then ‖X e‖^(k+1)+‖Y e‖^(k+1) else 0
  have pos (e:Bonds n):0≤h e := by by_cases he:e∈S <;> simp only [h,he,ite_true,ite_false] <;> positivity
  have local_ (q:Face (Per n)) : ‖angles S X q‖^(k+1)+‖angles S Y q‖^(k+1)≤∑j:Fin 4,h (edges q j) := by
    refine (add_le_add (maximum (angles S X q) (k+1)) (maximum (angles S Y q) (k+1))).trans_eq ?_
    rw [←sum_add_distrib]
    apply sum_congr rfl;intro j _
    by_cases hj:edges q j∈S <;> simp [h,angles,hj]
  calc
    _≤∑q∈set S,∑j:Fin 4,h (edges q j) := sum_le_sum (fun q _=>local_ q)
    _≤∑q:Face (Per n),∑j:Fin 4,h (edges q j) := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun q _ _=>sum_nonneg fun j _=>pos _)
    _≤6*∑e:Bonds n,h e := WilsonLocalPlaquetteMultiplicity.sum h pos
    _=_ := by simp [h,Finset.sum_ite_mem]

end YM.Integration.WilsonLocalPlaquetteBonds
