import YM.Integration.WilsonRunFormalMarkedStep
import YM.FormalBulk08.Spruce.Close

/-! Reclosed formal field transport on a chosen Wilson run. The coupling
substitution is part of each stage. With that convention the genuine forward
and inverse strings keep their coefficientwise valence at *every* depth. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryFormalMatrices

open Filter Real Function Lattice RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Exterior Stationary Lotus Shore Mesa Gorge City Cork Rift Lava
open Kemp Pose Glide Bank Dawn Wine Rial Roof Dove Series
open Planned.PrimaryIntegral295 Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato WilsonRunFormalMarkedStep
open scoped Classical BigOperators Matrix

variable {G : Gauge} (R : Run G) {d D : ℕ}
variable (L : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch)) (a : hue G) (depth : d<D)
private abbrev branches (i : ℕ) := (R.family.path.levels.blocks i 0).branches
private abbrev vacuum (N i : ℕ) :=
  Dove.model (K:=R.family.path.levels.clock.kernel) R.family.path.levels L (branches R) R.metals.O a N i

def reset (N i : ℕ) : Pence →+* Pence :=
  Roof.reborn a (destination R.family.path.levels N i) (L i) R.family.path.levels.clock.kernel
    (vacuum R L a N (i+1)) R.metals.O (branches R i)

private theorem chart (simple : G.Simple) (o : Loc G 1) (N i : ℕ) (live : i<N)
    (trained : d≤R.family.path.levels.clock.J (i+1)) :
    Colfax (slots (R.family.labels.level d)) (Pose.weight (R.family.labels.level d))
      (matrix R L a depth N i) (fun b=>Grail.heightK (R.family.S.block i) d (Pose.weight (R.family.labels.level d) b)) := by
  have next := normalized R L a depth simple o N (i+1) live
    (trained.trans (R.family.path.levels.fits.mono (Nat.le_succ _)))
  have story := (Dove.genu R.family.path.levels L (branches R) R.metals.O a R.alloy.B.ratio simple
    (i:=i+1) (N:=N) live).toStory
  exact Roof.performed o (R.family.labels.level d) (graph R L a depth N (i+1)) R.metals.O a
    (destination R.family.path.levels N i) (L i) (branches R i) (Elm.growL R.family.path.levels i)
    (vacuum R L a N (i+1)) R.family.params depth trained (R.family.path.levels.clock.adm i) story R.alloy.B.ratio next

private def within {I : Type*} (s : I→ℕ) (M : Matrix I I Pence) : Prop :=
  ∀ i j e, s j + e < s i → coeff e (M i j) = 0

private theorem initial {I : Type*} [DecidableEq I] (s : I→ℕ) : within s (1 : Matrix I I Pence) := by
  intro i j e high
  have neq : i ≠ j := by rintro rfl; omega
  rw [Matrix.one_apply,if_neg neq,map_zero]

private theorem product {I : Type*} [Fintype I] {s : I→ℕ} {M Q : Matrix I I Pence}
    (m : within s M) (q : within s Q) : within s (M*Q) := by
  intro i j e high
  rw [Matrix.mul_apply,map_sum]
  apply Finset.sum_eq_zero
  intro b _
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  have hx := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  by_cases suffix : s j+x.2<s b
  · rw [q b j _ suffix,mul_zero]
  · rw [m i b x.1 (by omega),zero_mul]

private theorem renamed {I : Type*} [Fintype I] [DecidableEq I] {s : I→ℕ} {M : Matrix I I Pence}
    (N i : ℕ) (h : within s M) : within s ((reset R L a N i).mapMatrix M) := by
  intro b y e high
  simp only [RingHom.mapMatrix_apply,Matrix.map_apply]
  unfold reset
  rw [Roof.rele]
  let clock := Roof.epoch a (destination R.family.path.levels N i) (L i) R.family.path.levels.clock.kernel
    (vacuum R L a N (i+1)) R.metals.O (branches R i)
  have fresh : coeff 0 (bookH clock * (PowerSeries.X : Pence)) = 0 := by rw [coeff_zero_eq_constantCoeff_apply,map_mul]; simp
  rw [subst_coeff fresh _ e e le_rfl]
  apply Finset.sum_eq_zero
  intro u hu
  rw [Finset.mem_range] at hu
  rw [h b y u (by omega),zero_mul]

/-- The independently prescribed field matrices and the actual dated
    coupling reset are recomposed in their original order on this run. -/
def strings (N : ℕ) : ℕ → ℕ → Tilework (R.family.labels.level d) × Tilework (R.family.labels.level d)
  | 0,_ => (1,1)
  | n+1,i =>
    let B := matrix R L a depth N i
    let σ : Tilework (R.family.labels.level d) →+* Tilework (R.family.labels.level d) := (reset R L a N i).mapMatrix
    let T := strings N n (i+1)
    (B*σ T.1,σ T.2*B⁻¹)

private theorem composite (simple : G.Simple) (o : Loc G 1) (N n i : ℕ)
    (live : i+n≤N) (gate : d≤R.family.path.levels.clock.J (i+1)) :
    let T := strings R L a depth N n i
    T.1*T.2=1 ∧ T.2*T.1=1 ∧ within (slots (R.family.labels.level d)) T.1 ∧ within (slots (R.family.labels.level d)) T.2 := by
  induction n generalizing i with
  | zero =>
    dsimp only [strings]
    exact ⟨one_mul _,one_mul _,initial _,initial _⟩
  | succ n ih =>
    let B := matrix R L a depth N i
    let σ : Tilework (R.family.labels.level d) →+* Tilework (R.family.labels.level d) := (reset R L a N i).mapMatrix
    let T := strings R L a depth N n (i+1)
    obtain ⟨oneF,oneB,rankF,rankB⟩ := ih (i+1) (by omega) (gate.trans (R.family.path.levels.fits.mono (Nat.le_succ _)))
    have step := chart R L a depth simple o N i (by omega) gate
    have unitF : B*B⁻¹=1 := Matrix.mul_nonsing_inv _ step.det
    have unitB : B⁻¹*B=1 := Matrix.nonsing_inv_mul _ step.det
    have forward : σ T.1*σ T.2=1 := by rw [←map_mul]; change σ (T.1*T.2)=1; rw [oneF,map_one]
    have backward : σ T.2*σ T.1=1 := by rw [←map_mul]; change σ (T.2*T.1)=1; rw [oneB,map_one]
    change (B*σ T.1)*(σ T.2*B⁻¹)=1 ∧ (σ T.2*B⁻¹)*(B*σ T.1)=1 ∧ _ ∧ _
    refine ⟨?_,?_,product step.bound (renamed R L a N i rankF),product (renamed R L a N i rankB) step.back.bound⟩
    · calc
        _ = B*((σ T.1*σ T.2)*B⁻¹) := by simp only [mul_assoc]
        _ = 1 := by rw [forward,one_mul,unitF]
    · calc
        _ = σ T.2*((B⁻¹*B)*σ T.1) := by simp only [mul_assoc]
        _ = 1 := by rw [unitB,one_mul,backward]

/-- One training threshold before every perturbative order, every later
    cutoff, and any number of reclosed steps. At coupling degree e a field
    with l original slots never produces more than l+e, in the graph itself
    or in either chronological matrix. -/
theorem reclosed (simple : G.Simple) (o : Loc G 1) :
    ∀ᶠ k : ℕ in atTop, ∀ (N n i : ℕ), k ≤ i → i+n ≤ N →
      let T := strings R L a depth N n i
      let F := R.family.labels.level d
      T.1*T.2=1 ∧ T.2*T.1=1 ∧
      (∀ b z e, slots F z+e < slots F b → coeff e (T.1 b z)=0 ∧ coeff e (T.2 b z)=0) ∧
      ∀ z f e r, slots F z+e < r → graph R L a depth N i z f e r=0 := by
  filter_upwards [R.family.path.levels.fits.deep.eventually_ge_atTop d] with k ready
  intro N n i ki live T F
  have gate := ready.trans (R.family.path.levels.fits.mono (ki.trans (Nat.le_succ i)))
  obtain ⟨p,q,h,j⟩ := composite R L a depth simple o N n i live gate
  refine ⟨p,q,fun b z e too=>⟨h b z e too,j b z e too⟩,?_⟩
  intro z f e r high
  by_contra notzero
  have bound := ((normalized R L a depth simple o N i (by omega) gate).officers z).fare.1 f e r notzero
  exact (not_lt_of_ge bound) high

end YM.Integration.WilsonPhysicalHistoryFormalMatrices

