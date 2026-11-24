import YM.Integration.WilsonLocalPlaquetteTaylor

/-! Only the original oriented Wilson plaquettes incident on changed
physical bonds remain in the signed action. All other group entries are
frozen at their actual compact values. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalPlaquetteField
open Set Function Finset Lattice Wilson RG WilsonPlaquetteIncidence WilsonLocalPlaquetteTaylor
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}
abbrev Bonds (n:Side) := Edge (Site n)
abbrev Angular (G:Gauge) (n:Side) := Bonds n→G.Color

def set (S:Finset (Bonds n)) : Finset (Face (Per n)) := univ.filter fun q=>∃i:Fin 4,edges q i∈S
def field (S:Finset (Bonds n)) (outside L R:Config G n) (X:Angular G n) (t:ℝ) : Config G n :=
  fun e=>if e∈S then L e*G.lieExp (t•X e)*R e else outside e

def pivot (S:Finset (Bonds n)) (outside L R:Config G n) (q:Face (Per n)) : Pivots G :=
  (fun i=>if edges q i∈S then L (edges q i) else outside (edges q i),
   fun i=>if edges q i∈S then R (edges q i) else 1)

def angles (S:Finset (Bonds n)) (X:Angular G n) (q:Face (Per n)) : Angles G :=
  fun i=>if edges q i∈S then X (edges q i) else 0

theorem filed (S:Finset (Bonds n)) (outside L R:Config G n) (X:Angular G n) (q:Face (Per n)) (t:ℝ) :
    faceValue (field S outside L R X t) q=loop (placed (pivot S outside L R q) (t•angles S X q)) := by
  have enter (i:Fin 4) : field S outside L R X t (edges q i) =
      placed (pivot S outside L R q) (t•angles S X q) i := by
    by_cases hi : edges q i∈S <;> simp [field,pivot,placed,angles,hi]
  rw [←head_zero]
  change (field _ _ _ _ _ _ (edges q 0)*field _ _ _ _ _ _ (edges q 1)*
    (field _ _ _ _ _ _ (edges q 2))⁻¹*(field _ _ _ _ _ _ (edges q 3))⁻¹)=_
  simp only [enter,loop]

theorem difference (S:Finset (Bonds n)) (outside L R:Config G n) (X Y:Angular G n) (t:ℝ) :
    energy (field S outside L R X t)-energy (field S outside L R Y t)=
      ∑q∈set S,(G.price (loop (placed (pivot S outside L R q) (t•angles S X q)))-
        G.price (loop (placed (pivot S outside L R q) (t•angles S Y q)))) := by
  simp only [energy,filed,←Finset.sum_sub_distrib]
  apply Eq.symm
  apply sum_subset (subset_univ _)
  intro q _ hq
  have untouched (i:Fin 4) : edges q i∉S :=
    fun hi=>hq (mem_filter.mpr ⟨mem_univ _,i,hi⟩)
  have eq : angles S X q=angles S Y q := by funext i;simp [angles,untouched i]
  rw [eq,sub_self]

theorem collar (S:Finset (Bonds n)) (X:Angular G n) {t:ℝ} (ht:0<t)
    (room:∀e∈S,t*‖X e‖<1) (q:Face (Per n)) : t*‖angles S X q‖<1 := by
  apply (lt_div_iff₀' ht).mp
  apply (pi_norm_lt_iff (one_div_pos.mpr ht)).mpr
  intro i
  by_cases hi : edges q i∈S
  · simpa [angles,hi] using (lt_div_iff₀' ht).mpr (room _ hi)
  · simpa [angles,hi] using (one_div_pos.mpr ht)

end YM.Integration.WilsonLocalPlaquetteField
