import YM.Integration.WilsonOrdinaryMeasuredTicket

/-! The fixed-ratio numerical test uses exactly four real *physical* two-site tables:
one at the mixed radii and three at the equal radii with fixed free entering fields. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryFourGram
open Filter Set Spec Climb OPE RG12 RG12.Frames RG17 SharpGram Trace.Pilot
open WilsonOrdinaryMixedGram WilsonOrdinaryNormalizedStep
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (J : ℝ → PhysMS.tower S) (d : ℕ)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field d

def signed (u : ℝ) (a : Fin 4 → ℝ) : ℝ := a 0 - a 1 - u*a 2 - u^2*a 3

def columns (s : ℝ) (A B : Module.End ℂ D) (v : D) : Fin 4 → D :=
  ![v, Pert.Scale.gear C.labels d s v, Pert.Scale.gear C.labels d s (A v), Pert.Scale.gear C.labels d s (B v)]

def radii (r s : ℝ) : Fin 4 → ℝ := ![s*r,r,r,r]

theorem split (r s u : ℝ) (A B : Module.End ℂ D) (v w : D) :
    mixed F J d r (s*r) v w - trialStep F J d r s (second d u A B) v w =
    signed u (fun j => mixed F J d r (radii r s j) (columns d s A B v j) w) := by
  let E := Pert.Scale.gear C.labels d s
  let M := mixed F J d r r
  have predicted : trialStep F J d r s (second d u A B) v w =
      M (E (second d u A B v)) w := rfl
  have unpack : E (second d u A B v) = E v + u • E (A v) + (u^2:ℝ) • E (B v) := by
    simp only [second,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.id_apply,map_add,map_smul]
    rw [←Complex.ofReal_pow]; simp only [Complex.coe_smul]
  rw [predicted,unpack]
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
  change _ = mixed F J d r (s*r) v w - M (E v) w - u*M (E (A v)) w - u^2*M (E (B v)) w
  ring

theorem error {u fee : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) (hf : 0 ≤ fee)
    (a b : Fin 4 → ℝ) (paid : ∀ i, |a i-b i| ≤ fee) :
    |signed u a - signed u b| ≤ 4*fee := by
  have scaled (k : ℕ) (i : Fin 4) : |u^k*(a i-b i)| ≤ fee := by
    rw [abs_mul,abs_of_nonneg (pow_nonneg h0 _)]
    exact (mul_le_mul_of_nonneg_left (paid i) (pow_nonneg h0 _)).trans
      (mul_le_of_le_one_left hf (pow_le_one₀ h0 h1))
  have s1 : |u*(a 2-b 2)| ≤ fee := by simpa using scaled 1 2
  have s2 := scaled 2 3
  obtain ⟨l0,h0'⟩ := abs_le.mp (paid 0)
  obtain ⟨l1,h1'⟩ := abs_le.mp (paid 1)
  obtain ⟨l2,h2'⟩ := abs_le.mp s1
  obtain ⟨l3,h3'⟩ := abs_le.mp s2
  apply abs_le.mpr; unfold signed
  constructor <;> linarith only [l0,h0',l1,h1',l2,h2',l3,h3']

end YM.Integration.WilsonOrdinaryFourGram
