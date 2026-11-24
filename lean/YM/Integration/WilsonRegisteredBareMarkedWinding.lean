import YM.Integration.OriginalIssuedMarkedRows
import YM.Integration.WilsonFiniteIncomingWindingCurrent

/-! Finite-volume inputs and cover partners for a registered bare curvature
source, with its own colour current, derivative address and fine placement. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonRegisteredBareMarkedWinding
open Function Finset Lattice Wilson RG Source Labels Marker WilsonCoeffUV
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding OriginalMarkedSourceComet
open IndependentSourcePathFamily
open scoped Classical BigOperators
variable {G : Gauge} {ι : Type} [DecidableEq ι] [Fintype ι]
variable {D k : ι → ℕ} {I : ι → Type} [∀ i, Fintype (I i)]

private def agrees {V : Type} [NormedAddCommGroup V] (B : Era G V) : Prop :=
  ∀ (n : Side) (a r : ℕ), B.1 n a r = Carp.plume (B.2 a r) n

private theorem sum_agrees {V B : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] {j : ℕ} (H : B → Era G V) (s : Finset B)
    (auth : ∀ b ∈ s, Auth j (H b)) (paired : ∀ b ∈ s, agrees (H b)) :
    agrees (∑ b ∈ s, H b) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro n i r; simp [plume_zero]
  | @insert b s hb ih =>
    rw [Finset.sum_insert hb]
    have u := fun b' (h : b' ∈ s) => auth b' (Finset.mem_insert_of_mem h)
    exact carousel (auth b (Finset.mem_insert_self ..)) (Auth.sum u)
      (paired b (Finset.mem_insert_self ..))
      (ih u fun b' h => paired b' (Finset.mem_insert_of_mem h))

omit [Fintype ι] in
private theorem primitive (D : ι → ℕ) (o : ι) {r : ℕ} (A : RG.Atom G r)
    (K : Knob (D o)) (x : Chamber) (e : ℕ) (p : Cover) :
    agrees (source D o A K x e p) := by
  let C := current A (claim (D o) K x)
  let B := volumeR C e
  let T := petal D o
  intro n j i
  change revolve (wrap n p) (T ∘ B.1 n j i) = plume (revolve p (T ∘ B.2 j i)) n
  rw [sigmaMint, plume_map _ (volume_price C one_pos e j i) (show 0 < steep 1 by
    unfold steep; norm_num) T n, aug_plane]

/-- Exact folding of all coefficient tensors of the named bare marked family.
It applies independently at every fine placement before any external test. -/
theorem original (X : ∀ i, I i → Seed G (D i)) (z : ι → Cover)
    (hX : ∀ i b, (X i b).rank ≤ k i + (X i b).head) (S : Finset ι)
    (n : Side) (a r : ℕ) :
    ((independent X z S).1 n a r) = plume ((independent X z S).2 a r) n := by
  by_cases h : ∃ i, S = {i}
  · obtain ⟨i, rfl⟩ := h
    rw [IndependentSourcePathFamily.singleton]
    let H (b : I i) :=
      let v := X i b
      source D i (colour v.path v.color v.weight v.quadrant) v.knob v.point v.head (z i)
    have u : ∀ b ∈ Finset.univ, Auth (k i) (H b) := fun b _ =>
      certified _ _ _ (fun g f => invariant _ _ _ _ g f) _ _ _ _ (hX i b) _
    exact sum_agrees H Finset.univ u
      (fun b _ => primitive D i _ (X i b).knob (X i b).point (X i b).head (z i)) n a r
  · have hz : independent X z S = 0 := by
      unfold independent
      exact Finset.sum_eq_zero fun i _ => dif_neg fun hi => h ⟨i, hi.symm⟩
    rw [hz]; exact (plume_zero ..).symm

/-- The registered source pays the incoming finite winding test on the
original and cover families, with its single authenticated before-test fee. -/
theorem registered {e m N : ℕ} (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m)
    (hN : m < N) (X : ∀ i, I i → Seed G (D i)) (w : Gear G → ℝ)
    (hw : ∀ B, 0 < w B) (Z : Finset ι) (cells : (ι → Cover) → ι → Site (loose Q.draws m).L)
    (hX : ∀ i b, (X i b).rank ≤ k i + (X i b).head) (y : ι → Cover) (n : Side) :
    let T := OriginalIssuedMarkedRows.input X Q hm w hw Z cells hX
    let σ := (Q.mint (m+1) (by omega)).σ
    let A := OriginalIssuedMarkedRows.fee (k:=k) X Q hm w
    ∀ S ⊆ Z, ∀ j ≤ e, ∀ l,
      MarkU (chartIn (loose Q.draws m) y (cells y)) S
        ((T.familyAt y S).1 (n*(loose Q.draws m).L) j l) ((T.familyAt y S).2 j l)
        (holt Q m hm σ (Q.mint (m+1) (by omega)).width).s
        ((diamond G e (mass k Z) σ * A)^S.card) := by
  intro T σ A S hS j hj l
  have hA := (IndependentSourcePathFamily.preblock X (k:=k) y Z e (w:=4 *
    max (w (Q.mint m hm).gear) σ) (mul_pos (by norm_num) ((hw _).trans_le (le_max_left ..))) hX).1
  let packet := flowOne Q Z (T.familyAt y) m N hm hN σ (Q.mint (m+1) (by omega)).width y
    (cells y) (T.empty y) (T.degree y) A hA (T.price y) n
  have paired := packet.shore S hS j hj l
  change MarkU (chartIn (loose Q.draws m) y (cells y)) S
    (Carp.plume ((T.familyAt y S).2 j l) (n*(loose Q.draws m).L)) ((T.familyAt y S).2 j l)
    (holt Q m hm σ (Q.mint (m+1) (by omega)).width).s
    ((diamond G e (mass k Z) σ * A)^S.card) at paired
  have eq := original X (chartIn (loose Q.draws m) y (cells y)) hX S (n*(loose Q.draws m).L) j l
  change ((T.familyAt y S).1 _ j l) = Carp.plume ((T.familyAt y S).2 j l) _ at eq
  rw [eq]
  exact paired

end YM.Integration.WilsonRegisteredBareMarkedWinding
end
