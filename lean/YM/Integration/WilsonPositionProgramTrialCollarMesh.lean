import YM.Integration.WilsonPositionProgramArithmeticBand

/-! The prescribed, already paid planting block supplies the auxiliary mesh.
Only the older starting date is chosen. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialCollarMesh
open Filter Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open Push.PriceCompiler WilsonPositionProgramCommonWindow WilsonPositionProgramInfraredWindow
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) (simple : G.Simple) (D : XSpace.Run) {a : Axis} {ε : ℝ}
local notation "Λ" => RG16.Lambda R.family.path.levels

def index (w : ℕ → ℕ) (n j : ℕ) : ℕ := elapsed (next w n) j

structure Corridor (start : ℕ) (w : ℕ → ℕ) (stage n j b : ℕ) : Prop where
  below : b≤n
  eligible : stage ≤ start+b
  spacing : R.family.S.a (start+n+j)/R.family.S.a (start+n) = (D.step (index w n j)).spacing
  blocks : ∀ k, (R.family.S.block ((start+b)+k)).val=D.ratio^(next w b k)
  older : elapsed w b+D.reserve*(index w n j)*(index w n j)=elapsed w n
  total : elapsed (next w b) (n+j-b)=D.reserve*(index w n j)*(index w n j)+index w n j

include simple in
theorem date {start : ℕ} {w : ℕ → ℕ}
    (stamps : ∀ k, (R.family.S.block (start+k)).val=D.ratio^(w k))
    (nested : ∀ k l, k≤l → w k ∣ w l) (stage : ℕ) {A : ℝ} (_nonneg : 0≤A) :
    ∀ᶠ n in atTop,∀ j : ℕ,
      Real.log (R.family.S.a (start+n) / R.family.S.a (start+n+j)) ≤ A * Λ (start+n) →
      ∃ b, Corridor R D start w stage n j b := by
  let L := Real.log (D.ratio:ℝ)
  have hL : 0<L := Real.log_pos (by exact_mod_cast
    (show 1<D.ratio from lt_of_lt_of_le (by decide) D.large))
  let debt := (D.reserve:ℝ)*(A/L)^2
  let head := (elapsed w stage:ℝ)
  have room := WilsonPositionProgramInfraredRoom.capacity R simple D start w stamps (debt+head+1) 2
  filter_upwards [room] with n funded j length
  let i := index w n j
  have blocks (h k : ℕ) : (R.family.S.block ((start+h)+k)).val=D.ratio^(next w h k) := by
    simpa only [next,Nat.add_assoc] using stamps (h+k)
  have spacing := fine_spacing R D (start+n) (next w n) (blocks n) j
  have logarithm : Real.log (R.family.S.a (start+n) / R.family.S.a (start+n+j)) = (i:ℝ)*L := by
    rw [←inv_div,spacing,Real.log_inv]
    change -Real.log ((D.den i:ℝ)⁻¹)=_
    simp [XSpace.Run.den,Real.log_pow,L]
  rw [logarithm] at length
  have upper : (i:ℝ) ≤ (A/L)*Λ (start+n) := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hL).mpr length
  have cost : (D.reserve*i*i : ℕ) ≤ debt*(Λ (start+n))^2 := by
    have watts := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg i) upper 2) (Nat.cast_nonneg D.reserve)
    calc
      ((D.reserve*i*i:ℕ):ℝ) = (D.reserve:ℝ)*(i:ℝ)^2 := by push_cast;ring
      _ ≤ _ := watts
      _ = _ := by dsimp [debt];ring
  have one : 1≤Λ (start+n) := by
    have hg := WilsonAdmissionScale.logarithm_pos R.family.path.levels (start+n)
    change 0<Real.log _ at hg
    change 1≤2+Real.log _
    linarith
  have hdoc : head+((D.reserve*i*i:ℕ):ℝ) < (elapsed w n:ℝ) := by
    have old := mul_le_mul_of_nonneg_left (one_le_pow₀ (n:=2) one) (show 0≤head from Nat.cast_nonneg _)
    nlinarith only [cost,funded,old,one_le_pow₀ (n:=2) one]
  have avail : D.reserve*i*i≤elapsed w n := by
    exact_mod_cast (show ((D.reserve*i*i:ℕ):ℝ) ≤ (elapsed w n:ℝ) by linarith only [hdoc,(show 0≤head from Nat.cast_nonneg _)])
  have portions (k : ℕ) (hk:k<n) : w k ∣ D.reserve*i*i := by
    have each : w k ∣ i := by
      change w k ∣ ∑ t ∈ range j, w (n+t)
      exact Finset.dvd_sum fun t _=>nested k (n+t) (by omega)
    exact dvd_mul_of_dvd_right each _
  obtain ⟨b,hb,paid⟩:=WilsonPositionProgramInfraredBlocks.close w nested n _ avail portions
  have early : stage≤b := by
    by_contra! no
    have bill : elapsed w b ≤ elapsed w stage := Finset.sum_le_sum_of_subset (Finset.range_mono no.le)
    have hnat : elapsed w stage+D.reserve*i*i<elapsed w n := by
      dsimp only [head] at hdoc
      exact_mod_cast hdoc
    omega
  refine ⟨b,hb,early.trans (Nat.le_add_left b start),spacing,blocks b,paid,?_⟩
  have both := WilsonPositionProgramInfraredWindow.append w b (n+j-b)
  rw [show b+(n+j-b)=n+j by omega,WilsonPositionProgramInfraredWindow.append w n j] at both
  change elapsed w n+i=elapsed w b+elapsed (next w b) (n+j-b) at both
  change elapsed (next w b) (n+j-b)=D.reserve*i*i+i
  omega

theorem original (purchase : WilsonPositionProgramArithmetic.course simple a ε R.kit) {d : ℕ}
    (hd : 0<d) (ratio : D.ratio=(3:ℕ)^d) :
    ∃ start : ℕ,∃ w : ℕ→ℕ, (∀ k, (R.family.S.block (start+k)).val=D.ratio^(w k)) ∧
      ∀ stage (A : ℝ), 0≤A → ∀ᶠ n in atTop,∀ j : ℕ,
      Real.log (R.family.S.a (start+n) / R.family.S.a (start+n+j)) ≤ A * Λ (start+n) →
      ∃ b, Corridor R D start w stage n j b := by
  obtain ⟨start,w,stamps,chain⟩ := WilsonPositionProgramArithmeticInfraredBlocks.nested R D purchase hd ratio
  exact ⟨start,w,stamps,fun stage _ h => date R simple D stamps chain stage h⟩

end YM.Integration.WilsonPositionProgramTrialCollarMesh
end
