import YM.WilsonMS.XSpace.QuietMS
/-!
# Free Gram rank on every physical subalphabet

Biweight matters: Wick-substitution in the bare columns may lower slot count,
so we need rank results also on such lower triangular blocks. Prove for finite
test measurements without treating Dirac evaluation as a supported profile.
Use the existing reflection Gram supplier to show measurements separate. Our
argument uses rectangular tests and a square recovery, not insisting a
specific common test makes the Gram positive. Needed before order-one and
higher frames (logs and powers are costly otherwise).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Reservoir
open Function Set Filter MeasureTheory Real Finset
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus
open Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Plane MS.Landau MS.Landau.Detect MS.Land MS.Menus MS.Theater
open Fiscal BMenu VisitH
open scoped BigOperators Topology Classical ComplexOrder
variable {G : Gauge} {d j k : ℕ}
local notation "BΨ" => Ensure.deck G

abbrev RowKey (G : Gauge) (d j : ℕ) :=
  { i : Glyph (Ensure.deck G) d // i.grade < j }
local notation "PlaceP" => RowKey G d j

/-- realization of low-slot subspace -/
def enroll (G : Gauge) (d j : ℕ) : (RowKey G d j → ℂ) →ₗ[ℂ] Sec G d :=
  (Pi.basisFun ℂ (RowKey G d j)).constr ℂ (fun i => glow i.val)

lemma enrollment (p : PlaceP → ℂ) : enroll G d j p = ∑ i, p i • glow i.val := by
  unfold enroll
  rw [Module.Basis.constr_apply_fintype]
  simp

lemma one_key (i : PlaceP) : enroll G d j ((Pi.basisFun ℂ _) i) = glow i.val :=
  Module.Basis.constr_basis ..

lemma enroll_coord (v : PlaceP → ℂ) (p : PlaceP) :
    (Daylight BΨ d).coord p.val (enroll G d j v) = v p := by
  rw [enrollment, map_sum]
  simp_rw [map_smul, ← Fiscal.shines]
  rw [Finset.sum_eq_single_of_mem p (Finset.mem_univ p)]
  simp
  intro i hi he
  have ht : i.val ≠ p.val := Subtype.val_injective.ne he
  simp [ht]

lemma enroll_inj (G : Gauge) (d j : ℕ) : Injective (enroll G d j) := by
  intro p q h
  funext i
  rw [← enroll_coord p i, h, enroll_coord]

abbrev lowerLand (G : Gauge) (d j : ℕ) :=
  LinearMap.range (enroll G d j)

lemma low_letter (p : Glyph BΨ d) (h : p.grade < j) : glow p ∈ lowerLand G d j :=
  ⟨_, one_key (show PlaceP from ⟨p, h⟩)⟩

lemma low_signed (p : PlaceP) (s : Signed) : ori s.ortho d (glow p.val) ∈ lowerLand G d j := by
  rw [turns]
  apply Submodule.sum_mem
  intro i hi
  by_cases ht : Bin.lines s p.val i = 0
  · simp [ht]
  exact
    Submodule.smul_mem _ _
      (low_letter i
        (by
          rw [← (Bin.bins s _ _ ht).2]
          exact p.property))

lemma stable (v : Sec G d) (s : Signed) (h : v ∈ lowerLand G d j) :
    reel d v ∈ lowerLand G d j ∧ ori s.ortho d v ∈ lowerLand G d j := by
  obtain ⟨p, rfl⟩ := h
  rw [enrollment]
  constructor
  · rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smulₛₗ, catches]
    exact Submodule.smul_mem _ _ (low_letter i.val i.property)
  rw [map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (low_signed i s)

private def z : E4 :=
  basis (3 : Axis)

private def pos2 : Points 2 :=
  pairPoints (-z) z

private lemma zP : 0 < z 3 := by simp [z]

private lemma z_ne : -z ≠ z := by
  intro h
  have he : -z 3 = z 3 := congr_arg (fun x : E4 => x 3) h
  linarith only [he, zP]

lemma full_equal (v w : Sec G d) :
    scene pos2 d ![ori (Signed.mirror 3).ortho _ (reel _ v), w] =
      Free.score (3 : Axis) z v.val w.val := by
  rw [Normalize.screen]
  unfold Free.score cabinet
  rw [show Table.Pairing.closedUp 3 (points fun _ : Fin 1 => z) (points fun _ : Fin 1 => z) = pos2
      from ?_]
  · congr 1
    funext i
    fin_cases i <;> rfl
  ext1 i
  refine Fin.addCases ?_ ?_ i
  · intro i
    fin_cases i
    apply PiLp.ext
    intro k
    rw [Table.Pairing.enter]
    change through 3 z k = (-z) k
    by_cases ht : k = 3 <;> simp [ht, through, z]
  intro i
  fin_cases i
  rw [Table.Pairing.leave]
  rfl

lemma stare_good (p : Sec G d) (h : p ≠ 0) :
    0 < scene pos2 d ![ori (Signed.mirror 3).ortho _ (reel _ p), p] := by
  rw [full_equal]
  exact Maxwell.Free.detects (3 : Axis) z zP p.val (fun hx => h (Subtype.ext hx))

def reading (p : Sec G d) (t : Test 2) (F : Prediction G d) : (Sec G d) →ₗ[ℂ] ℂ :=
  (F 2 t).toLinearMap ![p, 0] 1

lemma reads (p q : Sec G d) (t : Test 2) (F : Prediction G d) : reading p t F q = F 2 t ![p, q] := by
  unfold reading
  rw [MultilinearMap.toLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> simp

lemma blankG (p : Sec G d) (hv : p ∈ lowerLand G d j)
    (h : ∀ (a : PlaceP) t, reading (glow a.val) t (reference G d) p = 0) : p = 0 := by
  by_contra! he
  let q := ori (Signed.mirror 3).ortho d (reel d p)
  have ht : q ∈ lowerLand G d j := (stable _ _ (stable p (Signed.mirror 3) hv |>.1)).2
  obtain ⟨x, hx⟩ := ht
  have hs : ∀ a : PlaceP, scene pos2 d ![glow a.val, p] = 0 := fun a =>
    (Test.weak_null (Normalize.smooths _)).mp
      (fun t => by
        obtain H := h a t
        rw [reads, reflects] at H
        exact H)
      (pair_ok z_ne)
  let T := (scene pos2 d (G := G)).toLinearMap ![q, p] 0
  have H (y : Sec G d) : T y = scene pos2 d ![y, p] := by
    unfold T
    rw [MultilinearMap.toLinearMap_apply]
    congr 1
    ext1 i
    fin_cases i <;> simp
  obtain hZ := (stare_good p he).ne'
  apply hZ
  change scene pos2 d ![q, p] = _
  rw [← H, ← hx, enrollment, map_sum]
  exact Finset.sum_eq_zero fun i hi => by rw [map_smul, H, hs, smul_zero]

private lemma span_all {I E : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (P : I → E →ₗ[ℂ] ℂ) (h : ∀ x, (∀ i, P i x = 0) → x = 0) :
    ∃ S : Finset I, ∀ x, (∀ i ∈ S, P i x = 0) → x = 0 := by
  let K (S : Finset I) := ⨅ i : S, LinearMap.ker (P i.val)
  have hv : ∃ n : ℕ, ∃ S : Finset I, Module.finrank ℂ (K S) = n := ⟨_, ∅, rfl⟩
  obtain ⟨S, hS⟩ := Nat.find_spec hv
  refine ⟨S, fun x ht => h _ (fun i => ?_)⟩
  have hu : K (insert i S) ≤ K S :=
    le_iInf fun j =>
      iInf_le_of_le (⟨j.1, Finset.mem_insert_of_mem j.2⟩ : (insert i S : Finset I)) le_rfl
  have hK :=
    Submodule.eq_of_le_of_finrank_le hu
      (hS ▸
        Nat.find_min' hv
          (show ∃ t : Finset I, Module.finrank ℂ (K t) = Module.finrank ℂ (K (insert i S)) from
            ⟨_, rfl⟩))
  have he : x ∈ K (insert i S) :=
    hK.symm ▸
      (Submodule.mem_iInf _).mpr
        (fun j => LinearMap.mem_ker.mpr (ht j.1 j.2) : ∀ j : S, x ∈ LinearMap.ker _)
  exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp he ⟨i, Finset.mem_insert_self ..⟩)

abbrev Emblems (G : Gauge) (d j : ℕ) :=
  RowKey G d j × Test 2

/-- Graded Gram test family, using all earlier rows in the alphabet. -/
def atlas (S : Finset (Emblems G d j)) (P : FieldEnd G d) (A : Prediction G d) :
    (RowKey G d j → ℂ) →ₗ[ℂ] (S → ℂ) :=
  LinearMap.pi fun p => reading (P (glow p.val.1.val)) p.val.2 A ∘ₗ enroll G d j

/-- Any field sector has diagnostics of full free rank. Use this for
bounding the leading term of the otherwise dangerous finite amending matrix. -/
lemma test_full (G : Gauge) (d j : ℕ) :
    ∃ S : Finset (Emblems G d j), Injective (atlas S 1 (reference G d)) := by
  obtain ⟨S, h⟩ :=
    span_all (fun (i : Emblems G d j) => reading (glow i.1.val) i.2 (reference G d) ∘ₗ enroll G d j)
      (fun v H => by
        have hK : enroll G d j v = 0 := blankG _ (j := j) ⟨_, rfl⟩ fun p t => H (p, t)
        exact enroll_inj G d j (hK.trans (map_zero _).symm))
  refine ⟨S, fun x y H => sub_eq_zero.mp (h (x - y) (fun i hi => ?_))⟩
  exact
    show atlas S 1 (reference G d) (x - y) (show S from ⟨i, hi⟩) = 0 from
      by
      rw [map_sub, H, sub_self]
      rfl
end YM.WilsonMS.Reservoir
