import YM.Integration.MSFixedRatioFourierLifting

/-! The finite thermal Hessian minus its prescribed kinetic and loop response,
in the complete position sum with one original Wilson site held fixed. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.PhysicalWilsonRootedHessian
open Function Filter Finset Lattice Wilson RG Precision Exterior Gauge Marker MeasureTheory
open Comparison.RG02 Comparison.RG02.Assembly MSFixedRatioFourierLifting
open scoped Classical BigOperators RealInnerProductSpace Topology ContDiff

variable {G : Gauge} {n : Side}
abbrev Label (G : Gauge) (n : Side) := Site n × TypeFace 1 × G.ColorIndex

def unit (i : Label G n) : fieldDir G n 1 :=
  fun p => if p.1 = i.1 then if p.2 = i.2.1 then EuclideanSpace.basisFun G.ColorIndex ℝ i.2.2
    else 0 else 0

theorem unit_size (i : Label G n) : size (unit i) = 1 := by
  rcases i with ⟨x,a,j⟩
  have he (y : Site n) (b : TypeFace 1) (k : G.ColorIndex) :
      |unit (x,a,j) (y,b) k| = if y=x then if b=a then if k=j then 1 else 0 else 0 else 0 := by
    by_cases hy : y=x <;> by_cases hb : b=a <;> by_cases hk : k=j <;>
      simp_all [unit,EuclideanSpace.basisFun_apply,eq_comm]
  simp [size,he]

def coordinate (B : fieldDir G n 1) (i : Label G n) : ℝ :=
  B (i.1,i.2.1) i.2.2

theorem decompose (B : fieldDir G n 1) : B = ∑ i : Label G n, coordinate B i • unit i := by
  ext ⟨x,a⟩ k
  rw [Finset.sum_apply]
  change B (x,a) k = WithLp.ofLp (∑ i : Label G n, coordinate B i • unit i (x,a)) k
  rw [WithLp.ofLp_sum,Finset.sum_apply]
  have delta (i : Label G n) :
      WithLp.ofLp (coordinate B i • unit i (x,a)) k = if i=(x,a,k) then B (x,a) k else 0 := by
    rcases i with ⟨y,b,j⟩
    change B (y,b) j * (unit (y,b,j) (x,a) k) = _
    by_cases hxy : x=y <;> by_cases hab : a=b <;> by_cases hkj : k=j <;>
      simp_all [unit,EuclideanSpace.basisFun_apply,eq_comm]
  simp_rw [delta]
  simp

theorem expand (D : (fieldDir G n 1) [×2]→L[ℝ] ℝ) (u v : fieldDir G n 1) :
    D ![u,v] = ∑ f : Fin 2 → Label G n,
      (coordinate u (f 0) * coordinate v (f 1)) * D ![unit (f 0),unit (f 1)] := by
  let T : Fin 2 → fieldDir G n 1 := ![u,v]
  change D T = _
  calc
    _ = D (fun j => ∑ i : Label G n, coordinate (T j) i • unit i) :=
      congrArg D (funext fun j => decompose (T j))
    _ = ∑ f : Fin 2 → Label G n, D (fun j => coordinate (T j) (f j) • unit (f j)) :=
      D.toMultilinearMap.map_sum (fun j i => coordinate (T j) i • unit i)
    _ = _ := Finset.sum_congr rfl fun f _ => by
      rw [D.map_smul_univ (fun j => coordinate (T j) (f j)) (fun j => unit (f j)),
        Fin.prod_univ_two]
      have hx : (fun j => unit (f j)) = ![unit (f 0),unit (f 1)] := by
        funext j; fin_cases j <;> rfl
      rw [hx]
      rfl

theorem separation_side (x y : Site n) : separation x y ≤ n.val := by
  unfold separation pdist
  apply Finset.sup_le
  intro i _
  have h := lift_centers (x-y) i
  have ha : |lift (x-y) i|≤(n.val:ℤ) := abs_le.mpr ⟨by omega,by omega⟩
  rw [←Int.natCast_natAbs] at ha
  exact_mod_cast ha

def row (a : ℝ) (o : Site n) (D : Label G n → Label G n → ℝ) : ℝ :=
  ∑ u : TypeFace 1, ∑ j : G.ColorIndex, ∑ y : Site n, ∑ v : TypeFace 1, ∑ k : G.ColorIndex,
    Real.exp (a * separation o y) * |D (o,u,j) (y,v,k)|

def price (G : Gauge) (A c : ℝ) : ℝ :=
  ((Fintype.card (TypeFace 1):ℝ)*Fintype.card G.ColorIndex)^2 *
    (((Nat.factorial 8):ℕ):ℝ)*(4/c)^8*A/2

private theorem absorb {c : ℝ} (hc : 0 < c) (x : ℝ) (hx : 0 ≤ x) :
    x^8 * Real.exp (-(3*c/4)*x) ≤ ((Nat.factorial 8):ℝ) * (4/c)^8 * Real.exp (-(c/2)*x) := by
  have hh := Real.pow_div_factorial_le_exp _ (show 0 ≤ (c/4)*x by positivity) 8
  have hf : 0 < ((Nat.factorial 8):ℝ) := by positivity
  have hz : x^8 ≤ ((Nat.factorial 8):ℝ)*(4/c)^8*Real.exp ((c/4)*x) := by
    have hp := (div_le_iff₀ hf).mp hh
    have e : x^8 = (4/c)^8*((c/4*x)^8) := by
      have cancel : (4/c)*(c/4*x)=x := by field_simp [hc.ne']
      rw [←mul_pow,cancel]
    rw [e]
    exact (mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq (by ring)
  calc
    _ ≤ ((((Nat.factorial 8):ℝ)*(4/c)^8)*Real.exp ((c/4)*x))*Real.exp (-(3*c/4)*x) :=
      mul_le_mul_of_nonneg_right hz (Real.exp_pos _).le
    _ = _ := by
      have e : c/4*x+ -(3*c/4)*x= -(c/2)*x := by ring
      rw [mul_assoc,←Real.exp_add,e]

theorem weighted (D : Label G n → Label G n → ℝ) (o : Site n) {A c : ℝ}
    (hA : 0 ≤ A) (hc : 0 < c)
    (h : ∀ i j, |D i j| ≤ (Fintype.card (Site n) : ℝ)*A*Real.exp (-c*n.val)/2) :
    row (c/4) o D ≤ price G A c * Real.exp (-(c/2)*n.val) := by
  let z : ℝ := Fintype.card (Site n)
  let b : ℝ := Fintype.card (TypeFace 1)
  let d : ℝ := Fintype.card G.ColorIndex
  let l : ℝ := n.val
  have hz : 0 ≤ z := Nat.cast_nonneg _
  have hl : 0 ≤ l := Nat.cast_nonneg _
  have he (u : TypeFace 1) (j : G.ColorIndex) (y : Site n) (v : TypeFace 1) (k : G.ColorIndex) :
      Real.exp (c/4 * separation o y) * |D (o,u,j) (y,v,k)| ≤ z*A*Real.exp (-(3*c/4)*l)/2 := by
    have hs : (separation o y : ℝ) ≤ l := by
      change (separation o y:ℝ)≤(n.val:ℝ)
      exact_mod_cast separation_side o y
    calc
      _ ≤ Real.exp (c/4*l)*(z*A*Real.exp (-c*l)/2) := by
        apply mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs (by positivity)))
          (h _ _) (abs_nonneg _) (Real.exp_pos _).le
      _ = z*A*(Real.exp (c/4*l)*Real.exp (-c*l))/2 := by ring
      _ = _ := by
        have e : c/4*l+ -c*l= -(3*c/4)*l := by ring
        rw [←Real.exp_add,e]
  have ht := Finset.sum_le_sum (s:=Finset.univ) (fun u _ =>
    Finset.sum_le_sum (s:=Finset.univ) (fun j _ =>
      Finset.sum_le_sum (s:=Finset.univ) (fun y _ =>
        Finset.sum_le_sum (s:=Finset.univ) (fun v _ =>
          Finset.sum_le_sum (s:=Finset.univ) (fun k _ => he u j y v k)))))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at ht
  change row (c/4) o D ≤ b*(d*(z*(b*(d*(z*A*Real.exp (-(3*c/4)*l)/2))))) at ht
  have hc₁ : 0 ≤ (b*d)^2*A/2 := by positivity
  have hcard : z = l^4 := by simp [z,l]
  calc
    _ ≤ b*(d*(z*(b*(d*(z*A*Real.exp (-(3*c/4)*l)/2))))) := ht
    _ = ((b*d)^2*A/2)*(l^8*Real.exp (-(3*c/4)*l)) := by rw [hcard]; ring
    _ ≤ ((b*d)^2*A/2)*(((Nat.factorial 8):ℝ)*(4/c)^8*Real.exp (-(c/2)*l)) :=
      mul_le_mul_of_nonneg_left (absorb hc l hl) hc₁
    _ = _ := by unfold price b d l; ring

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {P : History G}
variable (Y : Bulk.Chain P) (N m p : ℕ) (hm : m < N)
    (F : Tree.Forest (P.levels.clock.op m p).ratio) (t : (P.levels.clock.op m p).Choices)
    (W : Bulk.Colors R G (P.S.side (m+1) p)) (r : ℕ)
local notation "n₀" => P.S.side m p
local notation "J" => P.levels.clock.J (m+1)
local notation "C" => Y.post.c J
local notation "A" => Y.post.Γ J * P.levels.clock.loopCap (m+1)
local notation "X" => fieldDir G n₀ 1

def difference : X [×2]→L[ℝ] ℝ :=
  iteratedFDeriv ℝ 2 (MSFixedRatioSignedReading.quadratic Y N m p hm F t W r) 0 -
    iteratedFDeriv ℝ 2 (draft (Y.kin.alpha N m) (P.rep N p m).path (P.rep N p m).clip) 0

def entry (i j : Label G n₀) : ℝ := difference Y N m p hm F t W r ![unit i,unit j]/2

/-- Evaluation reconstructs the full signed mixed Hessian on both original physical directions. -/
theorem evaluated (u v : X) :
    difference Y N m p hm F t W r ![u,v]/2 =
      ∑ f : Fin 2 → Label G n₀, coordinate u (f 0) * coordinate v (f 1) *
        entry Y N m p hm F t W r (f 0) (f 1) := by
  rw [expand (difference Y N m p hm F t W r) u v,Finset.sum_div]
  exact Finset.sum_congr rfl fun f _ => by unfold entry; ring

theorem chosen (hW : W.Standard) (hr : 2 ≤ r) (o : Site n₀) :
    row (C/4) o (entry Y N m p hm F t W r) ≤ price G |A| C * Real.exp (-(C/2)*(n₀).val) := by
  apply weighted _ _ (abs_nonneg A) (Y.post.posC J)
  intro i j
  have h := MSFixedRatioFourierLifting.actual Y N m p hm F t W r hW hr (unit i) (unit j)
  rw [unit_size,unit_size,mul_one,mul_one] at h
  unfold entry difference
  rw [sub_apply,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply h.trans
  rw [mul_assoc (Fintype.card (Site n₀) : ℝ) (Y.post.Γ J)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (le_abs_self A) (Nat.cast_nonneg _)) (Real.exp_pos _).le

theorem aligned (hW : W.Standard) (hr : 2 ≤ r) (o : Site n₀) {a : ℝ} (ha : a ≤ C/4) :
    row a o (entry Y N m p hm F t W r) ≤ price G |A| C * Real.exp (-(C/2)*(n₀).val) := by
  apply LE.le.trans _ (chosen Y N m p hm F t W r hW hr o)
  unfold row
  apply Finset.sum_le_sum; intro u _
  apply Finset.sum_le_sum; intro j _
  apply Finset.sum_le_sum; intro y _
  apply Finset.sum_le_sum; intro v _
  apply Finset.sum_le_sum; intro k _
  exact mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _))) (abs_nonneg _)

end YM.Integration.PhysicalWilsonRootedHessian
