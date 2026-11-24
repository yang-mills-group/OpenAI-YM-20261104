import YM.Integration.WilsonMaxwellThermometerSignedAxes
import YM.Integration.WilsonMaxwellThermometerChiralReading

/-! Classification of the proper-signed cap-four sources on the original
gauge-invariant Maxwell quotient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerLower
open Set Maxwell Maxwell.Free XSpace.Chiral
open WilsonMaxwellThermometerChiralSlots WilsonMaxwellThermometerSignedAxes
open WilsonMaxwellThermometerChiralReading
open scoped BigOperators
variable {G : Gauge}

def palette (G : Gauge) : Submodule ℂ (WickPol G) :=
  Submodule.span ℂ {p | p=1 ∨ ∃ s, p=polar G s}

theorem generators (W : Submodule ℝ (Flavor 0)) (h : ∀ s a, slot s a ∈ W) : W = ⊤ := by
  have ht : sig true = 1 := by rw [← WilsonMaxwellThermometerRotations.phase_cast]; norm_num [WilsonMaxwellThermometerRotations.phase]
  have hf : sig false = -1 := by rw [← WilsonMaxwellThermometerRotations.phase_cast]; norm_num [WilsonMaxwellThermometerRotations.phase]
  have E (a : P) : cell 0 (shard a) = (1/2:ℝ) • (slot true a + slot false a) := by
    simp only [slot, ht, hf]; module
  have B (a : P) : cell (shard (a+1)) (shard (a+2)) = (1/2:ℝ) • (slot true a - slot false a) := by
    simp only [slot, ht, hf]; module
  have axis : ∀ i j : Axis, i<j → (∃ a, i=0 ∧ j=shard a) ∨
      (∃ a, i=shard (a+1) ∧ j=shard (a+2)) ∨ (∃ a, j=shard (a+1) ∧ i=shard (a+2)) := by decide
  apply eq_top_iff.mpr; rw [← cell_span]; apply Submodule.span_le.mpr
  rintro z ⟨i,j,hij,rfl⟩
  rcases axis i j hij with ⟨a,rfl,rfl⟩ | ⟨a,rfl,rfl⟩ | ⟨a,rfl,rfl⟩
  · rw [E]; exact W.smul_mem _ (W.add_mem (h ..) (h ..))
  · rw [B]; exact W.smul_mem _ (W.sub_mem (h ..) (h ..))
  · rw [cell_skew, B]; exact W.neg_mem (W.smul_mem _ (W.sub_mem (h ..) (h ..)))

private theorem inner (s t : Bool) (c : P) (u v : Axis) (a b : P) :
    reflectPol (frame c u v).ortho (team G (slot s a) (slot t b)) =
      ((weight s u v a : ℝ)*(weight t u v b : ℝ)) • team G (slot s (a+c)) (slot t (b+c)) := by
  rw [orient_team, turns, turns]
  change duetL G 0 0 (_ • _) (_ • _) = _ • duetL G 0 0 _ _
  simp only [map_smul, LinearMap.smul_apply, smul_smul]; rw [mul_comm]

private theorem cycle_sum (s : Bool) (a : P) :
    (∑ c : P, team G (slot s (a+c)) (slot s (a+c))) = polar G s :=
  Equiv.sum_comp (Equiv.addLeft a) (fun b => team G (slot s b) (slot s b))

theorem preserved (s : Bool) (c : P) (u v : Axis) :
    reflectPol (frame c u v).ortho (polar G s) = polar G s := by
  rw [polar, map_sum]
  simp_rw [inner, square, one_smul]
  simpa only [polar, add_comm _ c] using cycle_sum (G:=G) s c

def average (G : Gauge) : WickPol G →ₗ[ℂ] WickPol G :=
  ∑ c : P, ∑ u : Axis, ∑ v : Axis, (reflectPol (frame c u v).ortho).toLinearMap

private theorem projected_pair (s t : Bool) (a b : P) :
    average G (team G (slot s a) (slot t b)) ∈ palette G := by
  simp only [average, LinearMap.sum_apply, AlgHom.toLinearMap_apply, inner]
  simp_rw [← Finset.sum_smul, ← Int.cast_mul, ← Int.cast_sum, sign_pairs]
  split_ifs with ht
  · obtain ⟨rfl,rfl⟩ := ht
    rw [← Finset.smul_sum, cycle_sum]
    exact (palette G).smul_of_tower_mem _ (Submodule.subset_span (Or.inr ⟨_,rfl⟩))
  · simp

private theorem projected (p q : Flavor 0) : average G (team G p q) ∈ palette G := by
  let S := (palette G).restrictScalars ℝ
  let A := (average G).restrictScalars ℝ
  have hp (s : Bool) (a : P) (w : Flavor 0) : average G (team G (slot s a) w) ∈ palette G := by
    let V := S.comap (A.comp (duetL G 0 0 (slot s a)))
    have hv : V = ⊤ := generators V (fun t b => projected_pair s t a b)
    exact show w ∈ V from hv ▸ Submodule.mem_top
  let V := S.comap (A.comp ((duetL G 0 0).flip q))
  have hv : V = ⊤ := generators V (fun s a => hp s a q)
  exact show p ∈ V from hv ▸ Submodule.mem_top

theorem classified (g : G.Simple) (p : WickPol G) (hp : p ∈ shellSector G 4)
    (fixed : ∀ (c : P) (u v : Axis), reflectPol (frame c u v).ortho p = p) : p ∈ palette G := by
  let W := (palette G).comap (average G)
  have h1 : (1 : WickPol G) ∈ W := by
    change average G 1 ∈ palette G
    simp only [average, LinearMap.sum_apply, AlgHom.toLinearMap_apply, map_one]
    exact (palette G).sum_mem fun c _ => (palette G).sum_mem fun u _ =>
      (palette G).sum_mem fun v _ => Submodule.subset_span (Or.inl rfl)
  have ht : Teams G 0 0 ≤ W := by
    apply Submodule.span_le.mpr; rintro z ⟨a,b,rfl⟩; exact projected a b
  have hbase : BottomOnly G ≤ W := by
    apply Submodule.span_le.mpr; rintro x (rfl : x=1); exact h1
  have hc : average G p ∈ palette G := sup_le hbase ht ((low_support g) ▸ hp)
  have scaled : average G p = (48:ℂ) • p := by
    simp only [average, LinearMap.sum_apply, AlgHom.toLinearMap_apply, fixed,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [scaled] at hc
  simpa only [smul_smul, show (48:ℂ)⁻¹*48=1 by norm_num, one_smul] using
    (palette G).smul_mem (48:ℂ)⁻¹ hc

end YM.Integration.WilsonMaxwellThermometerLower
