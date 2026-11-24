import YM.Integration.WilsonOriginalStarSceneRead
import YM.Integration.WilsonOriginalStarPrimaryCatalog

/-! The registered reporting rows have a common original healthy halo at a late mesh.
The mark on the scalar survives every physical flag. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalStarSceneMasked
open Function Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Earn Sunrise Affinity
open Push.AbsoluteSums.Animals
open PhysicalNext.Repeat.Legato WilsonOriginalStarSceneWords WilsonOriginalStarSceneRows
open WilsonOriginalStarSceneRead ActualRunPhysicalPages
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {V T : Type} [DecidableEq V] [Fintype V]
  (d : V → ℕ) {n : Side} (o : V → Site n) (σ g τ : ℝ)
  (v : (j:V)→R.family.label (d j)) (t : V→T→ℂ)

def range := univ.sup (fun i:Entry R d=>(raw R d i).length)

theorem ground (B : BudgetPoint) (aperture : range R d ≤ B.B) (i : Entry R d) :
    (rows R d o σ g τ v t i).ground B = neighbors (B.B+1) (o (root R d i)) := by
  apply Row.cleared
  change (binder o _).length+(raw R d i).length ≤ B.B
  rw [WilsonOriginalStarSceneRows.length,zero_add]
  exact (le_sup (f:=fun j:Entry R d=>(raw R d j).length) (mem_univ i)).trans aperture

theorem tests {𝕜 : Type} [RCLike 𝕜] [NormedAlgebra 𝕜 ℂ] {Y:V→Type}
    [∀j,AddCommGroup (Y j)] [∀j,Module 𝕜 (Y j)]
    (K : ∀j,Submodule 𝕜 (Y j)) (A:∀j,Set (Y j))
    (u : V → Wallet A → ℂ) (read : ∀j, Attn K A {j} (u j)) :
    Tableau K A (rows R d o σ g τ v u) := by
  refine ⟨fun i=>?_⟩
  let c:=((normalizer (raw R d i) σ:ℝ):ℂ)*scalar R d g τ v i
  exact (read (root R d i)).linear (LinearMap.mul 𝕜 ℂ c)

omit [Fintype V] in
private theorem send_sum {ι : Type} [Fintype ι] {J : Census V} (s:J.Mode) (a:ι→ℂ) :
    Poly.send s (∑i,a i) = ∑i,Poly.send s (a i) := by
  ext j
  simp only [Poly.part_send,Poly.part_sum]
  by_cases h:j=s <;> simp [h]

variable (N p k : ℕ) (h : k ≤ N) (sites : V → Site (R.family.side k p))
set_option quotPrecheck false
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N p k
local notation "B₀" => (R.family.path.rep N p k).p
local notation "X" => rows R d sites σ g₀ (B₀).threshold v t
local notation "J" => Stock.census V
local notation "P" => rendered (X) B₀ g₀
local notation "S" j:max => kernel R N p k (d j) ((R.family.labels.level (d j)).core (v j)) (sites j)

include h in
theorem whole (aperture : range R d ≤ (B₀).B) (x:T) (U : Config G (R.family.side k p)) :
    ((P).log x U) = ∑j:V,Poly.send ((J).fire j)
      (t j x * (v j 0 + masked (B₀).threshold (neighbors ((B₀).B+1) (sites j)) (S j) U)) := by
  rw [Lamps.log,tsum_fintype,Fintype.sum_sum_type,Fintype.sum_sigma,←Finset.sum_add_distrib]
  apply sum_congr rfl
  intro j _
  have clearOne : (P).light x (.inl j) U=(X (.inl j)).nominal g₀ x U:=by
    change (if constant R d (.inl j) then _ else _) = _
    exact if_pos (show constant R d (.inl j) from trivial)
  have roots (s:WilsonOriginalStarLaurentWallet.Socket R (d j)):
      (P).ground (.inr ⟨j,s⟩)=neighbors ((B₀).B+1) (sites j):=ground R d sites σ g₀ _ v t _ aperture _
  have graded : (∑s:WilsonOriginalStarLaurentWallet.Socket R (d j), (P).light x (.inr ⟨j,s⟩) U)=
      t j x * masked (B₀).threshold (neighbors ((B₀).B+1) (sites j)) (S j) U:=by
    by_cases full:Healthy (B₀).threshold (neighbors ((B₀).B+1) (sites j)) U
    · rw [masked_eq _ _ _ _ full,←monomials R d σ v t N p k h sites j x U]
      apply sum_congr rfl
      intro s _
      rw [Lamps.light,if_neg (show ¬(P).clear (.inr ⟨j,s⟩) from not_false),roots,masked_eq _ _ _ _ full]
      rfl
    · rw [masked_ne _ _ _ _ full,mul_zero]
      apply sum_eq_zero
      intro s _
      rw [Lamps.light,if_neg (show ¬(P).clear (.inr ⟨j,s⟩) from not_false),roots]
      exact masked_ne _ _ _ _ full
  change Poly.send ((J).fire j) ((P).light x (.inl j) U) +
    ∑s:WilsonOriginalStarLaurentWallet.Socket R (d j),Poly.send ((J).fire j) ((P).light x (.inr ⟨j,s⟩) U)=_
  rw [←send_sum,clearOne,scalar_read,graded,mul_add,Extra.Trajectories.send_add]

end YM.Integration.WilsonOriginalStarSceneMasked
