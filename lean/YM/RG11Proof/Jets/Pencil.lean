import YM.RG11Proof.Jets.Change

/-!
# Joint position-detector equation at the current coefficient

At any positive order, the as yet undetermined coefficients of the coupling
and all columns of a near-identity field change enter the transformed array by
one fixed (free orbit derivative, order-one coefficient) pencil. This includes
the possibility of coupling coefficients partly accounted for by field-basis
choices; do not invert the coupling alone without killing this mixing.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG11.Jets
open PowerSeries YM.PertExtension.Position
open scoped BigOperators Classical

section identity
variable {R J P : Type*} [CommRing R] [Fintype J] {arity : P→ℕ}

-- Extend Strike.evaluation to an array with simultaneous change in
-- numerical value, INCLUDING its amplitude coefficients at each transformed slot.
local notation "slots" => PertExtension.Position.insert

def framePencil (a : Mark J arity → R) (A X : Square J R) (v : Mark J arity) : R :=
  coeff 1 (slots J arity (fun w=> PowerSeries.C (a w))
    (fun i j=> PowerSeries.C (A i j)+PowerSeries.C (X i j)*PowerSeries.X) v)

/-- The amplitude part. -/
private theorem strike_amplitude {n : ℕ} {a b : ArrayAt J R arity} {u : Mark J arity → R}
    (hn : 0<n) (H : ∀ w, Strike n (a w) (b w) (u w)) (f : Square J R⟦X⟧) (v : Mark J arity) :
    Strike n (slots J arity a (fun i j=>f i j) v) (slots J arity b (fun i j=>f i j) v)
    (slots J arity u (fun i j=>constantCoeff (f i j)) v) := by
  unfold PertExtension.Position.insert
  apply Strike.sum; intro i _
  simpa only [mul_zero,add_zero,map_prod] using
    ((H ⟨v.1,i⟩).mul hn (Strike.same (∏ j,f (v.2 j) (i j))))

theorem strike_action {n : ℕ} {A : ArrayAt J R arity} {p q : Change R J}
    {X : Square J R} {c : R} (hn : 0<n) (hz : Anchored p.g)
    (h : Strike n p.g q.g c) (h' : ∀ i j, Strike n (p.Z i j) (q.Z i j) (X i j)) (v : Mark J arity) :
    Strike n (p.act A v) (q.act A v)
      (framePencil (fun w=>constantCoeff (A w)) (piece 0 p.Z) X v +
      slots J arity (fun w => tangent (A w)*c) (fun i j=>piece 0 p.Z i j) v) := by
  have he := Strike.evaluation (a:=fun w=> PowerSeries.subst p.g (A w)) (u:=fun i j=>X i j) (v:=v) hn h'
  have f := strike_amplitude (n:=n) hn (fun w=>strike_recouple (A w) hn hz h) q.Z v
  have ht : ∀ i j, constantCoeff (q.Z i j) = coeff 0 (p.Z i j) := fun i j=>by
    rw [← coeff_zero_eq_constantCoeff_apply]; exact ((h' i j).lower 0 hn).symm
  have hw := strike_trans he f
  simpa only [framePencil,Change.act,piece_apply,base_compose _ _ hz,ht,
    PowerSeries.coeff_zero_eq_constantCoeff_apply] using hw

variable [DecidableEq J]
/-- Infinitesimal simultaneous field-basis derivative. With this probe definition,
no engineering or reflection shift is applied to `v` (choose `P` to include
those desired; support/kinematics admissibility must be represented in `P`).
-/
def orbit (a : Mark J arity → R) (v : Mark J arity) (M : Square J R) : R :=
  ∑ i, ∑ j, M (v.2 i) j * a ⟨v.1, Function.update v.2 i j⟩

/-- The displayed row-by-row formula matches first coefficient of the
insert operation along `I + X t`. -/
theorem formula (a : Mark J arity → R) (v : Mark J arity) (M : Square J R) :
    orbit a v M = framePencil a 1 M v := by
  classical
  let m := arity v.1
  let I := Fin m
  let u : I→J := v.2
  let d (j k : J) : R := (1:Square J R) j k
  let K (w : I→J) (i : I) := PowerSeries.C (d (u i) (w i)) +
      PowerSeries.C (M (u i) (w i))* PowerSeries.X
  have hz (w : I→J) (s : Finset I) :
      constantCoeff (∏ i∈s,K w i) = ∏ i∈s,d (u i) (w i) := by
    simp [K]
  have h₁ (w : I→J) (s : Finset I) :
      coeff 1 (∏ i∈s,K w i) =
       ∑ i∈s, M (u i) (w i) * ∏ k∈s.erase i,d (u k) (w k) := by
    induction s using Finset.induction_on with
    | empty => simp [PowerSeries.coeff_one]
    | insert i s he hh =>
      rw [Finset.prod_insert he, PowerSeries.coeff_one_mul,hz, hh,Finset.sum_insert he]
      have hu : coeff 1 (K w i) = M (u i) (w i) := by simp [K]
      have hd : constantCoeff (K w i)=d (u i) (w i) := by simp [K]
      rw [hu, hd, Finset.sum_mul]
      rw [Finset.erase_insert he]
      congr 1
      apply Finset.sum_congr rfl; intro b hb
      have hf : i≠b := fun h=> he (h ▸ hb)
      rw [Finset.erase_insert_of_ne hf, Finset.prod_insert (by simp [he])]
      ring
  have he (w : I→J) (i : I) : (∏ k∈Finset.univ.erase i,d (u k) (w k)) =
      if w=Function.update u i (w i) then 1 else 0 := by
    split
    · rename_i hw; refine Finset.prod_eq_one ?_; intro j hj
      have hj := (Finset.mem_erase.mp hj).1
      have hww := congrFun hw j; rw [Function.update_of_ne hj] at hww
      simp [d,hww]
    rename_i h
    obtain ⟨j,hj⟩ := Function.ne_iff.mp h
    have hk : j≠i := by intro h; subst j; exact hj (by simp)
    rw [Function.update_of_ne hk] at hj
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hk,Finset.mem_univ _⟩) (Matrix.one_apply_ne hj.symm)
  unfold framePencil PertExtension.Position.insert
  change (orbit a v M) = coeff 1 (∑ w : I→J, PowerSeries.C (a ⟨v.1,w⟩) * ∏ i, K w i)
  simp_rw [map_sum, PowerSeries.coeff_C_mul,h₁,he,Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold orbit; apply Finset.sum_congr rfl; intro i _
  let t (w : I→J) (j : J) := if w=Function.update u i j then
       a ⟨v.1,w⟩ * M (u i) (w i) else 0
  have hw (w : I→J) : a ⟨v.1,w⟩ * (M (u i) (w i) * if w=Function.update u i (w i) then 1 else 0)=∑ j,t w j := by
    rw [Finset.sum_eq_single_of_mem (w i) (Finset.mem_univ _) (fun j _ hj=> ?_)]
    · unfold t; split <;> simp
    have hh : w≠Function.update u i j := by
      intro he; apply hj; simpa using (congrFun he i).symm
    simp [t,hh]
  change _ = ∑ w : I→J, a _ * (_ * _)
  simp_rw [hw]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_eq_single_of_mem (Function.update u i j) (Finset.mem_univ _) (fun x _ hx=> by simp [t,hx])]
  simp [t,u]; -- let congr
  exact mul_comm ..

def orbitL (a : Mark J arity→R) (v : Mark J arity) : Square J R →ₗ[R] R where
  toFun := orbit a v
  map_add' := by
    intro x y; unfold orbit; simp [Matrix.add_apply,add_mul,Finset.sum_add_distrib]
  map_smul' := by
    intro t x; unfold orbit; simp [Matrix.smul_apply,← Finset.mul_sum,mul_assoc]

/-- Field derivative and reference first coefficient acting as one linear pencil. -/
def pencil (A : ArrayAt J R arity) (v : Mark J arity) : Square J R × R →ₗ[R] R where
  toFun u := orbitL (fun w=>constantCoeff (A w)) v u.1 + tangent (A v)*u.2
  map_add' := by
    intro x y; simp only [Prod.fst_add,Prod.snd_add,map_add,mul_add]; abel
  map_smul' := by intro t x; simp only [Prod.smul_fst,Prod.smul_snd,map_smul,smul_eq_mul,mul_add,RingHom.id_apply]; ring

theorem pencil_action {n : ℕ} {A : ArrayAt J R arity} {p q : Change R J}
    {X : Square J R} {c : R} (hn : 0<n) (hz : Anchored p.g) (hZ : nearId p.Z)
    (h : Strike n p.g q.g c) (h' : ∀ i j, Strike n (p.Z i j) (q.Z i j) (X i j)) (v : Mark J arity) :
    Strike n (p.act A v) (q.act A v) (pencil A v (X,c)) := by
  have hh := strike_action (A:=A) hn hz h h' v
  unfold nearId at hZ
  rw [hZ, ← formula,show (fun i j=> (1:Square J R) i j) = (fun (i j : J) => if i=j then (1:R) else 0) from rfl] at hh
  -- classical dec mismatch
  classical
  convert! hh using 1
  trans orbit (fun w => constantCoeff (A w)) v X + tangent (A v)*c
  · rfl
  congr 1
  convert! (insert_one (fun w => tangent (A w)*c) v).symm using 1
  congr!
end identity
end YM.RG11.Jets
