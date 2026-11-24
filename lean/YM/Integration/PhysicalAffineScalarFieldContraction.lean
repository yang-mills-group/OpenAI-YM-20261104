import YM.Integration.PhysicalCoarseFieldBasis
import YM.Push.FREE_RESOLVENT.TrackBill
import YM.Push.FREE_RESOLVENT.TensorPrice

/-! Summation over the independent coarse field keys and arbitrary dense
coarse test fields, retaining the original held site and external tag. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarFieldContraction
open Filter Function Lattice Wilson RG Pressure FreeResolvent FreeResolvent.Affine FreeResolvent.Mark
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius

variable {X ι κ : Type*} [Fintype ι] [Fintype κ]

def distance (D : Cost X) (o : X) (p : ι→X) (q : κ→X) {n : ℕ} (t : κ) (l : Fin n→ι) :=
  D.d o (q t)+Stars.rays D o (p ∘ l)

/-- The held translation root costs no summation volume. -/
theorem sum (D : Cost X) (o : X) (p : ι→X) (q : κ→X) (n : ℕ) (s M V W : ℝ)
    (hm : 0≤M) (hv : D.Volume p s V) (hw : D.Volume q s W)
    (f : κ→(Fin n→ι)→ℝ) (h : ∀ t l, Real.exp ((2*s)*distance D o p q t l)*|f t l|≤M) :
    ∑ t, ∑ l : Fin n→ι, Real.exp (s*distance D o p q t l)*|f t l|≤(W*V^n)*M := by
  classical
  let v := fun j => D.weight (-s) o (p j)
  let w := fun t => D.weight (-s) o (q t)
  have e (t : κ) (l : Fin n→ι) : Real.exp (s*distance D o p q t l)*|f t l|≤(w t*∏ k,v (l k))*M := by
    let d := distance D o p q t l
    have hp : w t*∏ k,v (l k) = Real.exp (-s*d) := by
      unfold w v d distance Stars.rays Cost.weight
      rw [mul_add,Real.exp_add,Finset.mul_sum,Real.exp_sum]; rfl
    rw [hp]
    calc
      Real.exp (s*d)*|f t l|=Real.exp (-s*d)*(Real.exp (2*s*d)*|f t l|) := by
        rw [←mul_assoc,←Real.exp_add,show -s*d+2*s*d=s*d by ring]
      _≤Real.exp (-s*d)*M := mul_le_mul_of_nonneg_left (h t l) (Real.exp_pos _).le
  apply (Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun l _ => e t l).trans
  simp_rw [←Finset.sum_mul,←Finset.mul_sum,←Fintype.prod_sum (fun _ : Fin n => v),
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (mul_le_mul (hw.bound o)
    (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => D.weight_nn ..) (hv.bound o) n)
    (pow_nonneg (Finset.sum_nonneg fun _ _ => D.weight_nn ..) _) ((Finset.sum_nonneg fun _ _ => D.weight_nn ..).trans (hw.bound o))) hm

omit [Fintype ι] [Fintype κ] in
private theorem single_volume (D : Cost X) (o : X) {s : ℝ} (hs : 0≤s) :
    D.Volume (fun _ : PUnit => o) s 1 := by
  constructor; intro x; simp only [Fintype.sum_unique]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (D.nonneg x o))

theorem site_volume (c : Side) {s : ℝ} (hs : 0<s) :
    (native c).Volume (id : Site c→Site c) s (torusPay PUnit s) :=
  (volume c PUnit s hs).comp (e:=fun u : Site c => (u,PUnit.unit)) fun _ _ h => congrArg Prod.fst h

variable {G : Gauge} {c : Side}

/-- Expansion in every independent coarse direction, with the original
coarse input and its original complete Lie color. -/
theorem expand {n : ℕ} (D : ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec G c 1) ℝ)
    (B : Fin n→Vec G c 1) : D B=∑ l : Fin n→ raw G c, (∏ i,B i (l i))*D (ray G c ∘ l) := by
  simpa only [smul_eq_mul] using PhysicalCoarseFieldBasis.expand D B

/-- Arbitrary independent fields may grow away from the root up to the
spent spatial weight. The original external tree weight stays retained. -/
structure Root {κ : Type*} [Fintype κ] (n : ℕ) (s : ℝ) (o : Site c) (q : κ→Site c) (f : κ→Vec G c 1→ℝ) (M : ℝ) : Prop where
  coefficients : ∑ t, ∑ l : Fin n→ raw G c, Real.exp (s*distance (native c) o hearth q t l)*
    |iteratedFDeriv ℝ n (f t) 0 (ray G c ∘ l)| ≤ M
  fields : ∀ (B : Fin n→Vec G c 1) (A : Fin n→ℝ), (∀ i,0≤A i) →
    (∀ i j, |B i j|≤A i*(native c).weight s o (hearth j)) →
    ∑ t, (native c).weight s o (q t)*|iteratedFDeriv ℝ n (f t) 0 B| ≤ (∏ i,A i)*M

theorem Root.congr {κ : Type*} [Fintype κ] {n : ℕ} {s M : ℝ} {o : Site c} {q : κ→Site c}
    {f h : κ→Vec G c 1→ℝ} (H : Root n s o q f M) (E : ∀ t, f t =ᶠ[𝓝 0] h t) : Root n s o q h M := by
  have eqD (t : κ) : iteratedFDeriv ℝ n (f t) 0=iteratedFDeriv ℝ n (h t) 0 :=
    ((E t).iteratedFDeriv ℝ n).self_of_nhds
  refine ⟨by simpa only [←eqD] using H.coefficients,?_⟩
  intro B A hA hB; simpa only [←eqD] using H.fields B A hA hB

variable (G c) in
theorem contract {κ : Type*} [Fintype κ] {n : ℕ} (s : ℝ) (o : Site c) (q : κ→Site c) (f : κ→Vec G c 1→ℝ) (M : ℝ)
    (h : ∑ t, ∑ l : Fin n→ raw G c, Real.exp (s*distance (native c) o hearth q t l)*
      |iteratedFDeriv ℝ n (f t) 0 (ray G c ∘ l)| ≤ M) : Root n s o q f M := by
  classical
  refine ⟨h,?_⟩; intro B A hA hB
  let D (t : κ) := iteratedFDeriv ℝ n (f t) 0
  have hp (l : Fin n→ raw G c) : |∏ i,B i (l i)| ≤ (∏ i,A i)*∏ i,(native c).weight s o (hearth (l i)) := by
    rw [Finset.abs_prod,←Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => hB i (l i)
  have hd (t : κ) (l : Fin n→ raw G c) : (native c).weight s o (q t)*(∏ i,(native c).weight s o (hearth (l i))) =
      Real.exp (s*distance (native c) o hearth q t l) := by
    unfold distance Stars.rays Cost.weight; rw [mul_add,Real.exp_add,Finset.mul_sum,Real.exp_sum]; rfl
  have ht (t : κ) : (native c).weight s o (q t)*|D t B|≤(∏ i,A i)*∑ l : Fin n→ raw G c,
      Real.exp (s*distance (native c) o hearth q t l)*|D t (ray G c ∘ l)| := by
    rw [expand (D t) B]; apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs ..) ((native c).weight_nn ..)).trans
    rw [Finset.mul_sum,Finset.mul_sum]; apply Finset.sum_le_sum; intro l _
    simpa only [abs_mul,←hd,mul_assoc,mul_left_comm,mul_comm] using mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hp l) (abs_nonneg (D t (ray G c ∘ l)))) ((native c).weight_nn s o (q t))
  exact (Finset.sum_le_sum fun t _ => ht t).trans (by rw [←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left h (Finset.prod_nonneg fun i _ => hA i))

/-- Standard independent inputs need no weighted-test hypothesis. -/
theorem Root.bounded {κ : Type*} [Fintype κ] {n : ℕ} {s M : ℝ} {o : Site c} {q : κ→Site c} {f : κ→Vec G c 1→ℝ}
    (H : Root n s o q f M) (hs : 0≤s) (B : Fin n→Vec G c 1) :
    ∑ t,(native c).weight s o (q t)*|iteratedFDeriv ℝ n (f t) 0 B| ≤ (∏ i,‖B i‖)*M := by
  apply H.fields B (fun i => ‖B i‖) (fun _ => norm_nonneg _)
  intro i j
  calc |B i j| ≤ ‖B i‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (B i) j
       _ ≤ _ := le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (mul_nonneg hs ((native c).nonneg o (hearth j))))

/-- The independent mixed forms also sum in actual multilinear operator
norm, with the changed-tree translation still held in the spatial weight. -/
theorem Root.operators {κ : Type*} [Fintype κ] {n : ℕ} {s M : ℝ} {o : Site c} {q : κ→Site c} {f : κ→Vec G c 1→ℝ}
    (H : Root n s o q f M) (hs : 0≤s) :
    ∑ t,(native c).weight s o (q t)*‖iteratedFDeriv ℝ n (f t) 0‖ ≤ M := by
  classical
  let u (t : κ) := ∑ l : Fin n→ raw G c, Real.exp (s*Stars.rays (native c) o (hearth ∘ l))*
    |iteratedFDeriv ℝ n (f t) 0 (ray G c ∘ l)|
  have ht (t : κ) : ‖iteratedFDeriv ℝ n (f t) 0‖≤u t := by
    have sub : Root n s o (fun _ : PUnit.{1} => o) (fun _ => f t) (u t) :=
      contract G c s o _ _ _ (by simpa only [distance,Cost.self,zero_add,Fintype.sum_unique] using le_refl (u t))
    refine ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (abs_nonneg _)) ?_
    intro B
    simpa only [Fintype.sum_unique,Cost.weight_self,one_mul,Real.norm_eq_abs,mul_comm (u t)] using sub.bounded hs B
  apply (Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (ht t) ((native c).weight_nn ..)).trans
  simpa only [u,distance,Cost.weight,mul_add,Real.exp_add,Finset.mul_sum,mul_assoc] using H.coefficients

/-- Application of the finite product bound to a genuine regular scalar. -/
theorem regular (G : Gauge) (c : Side) {n : ℕ} (τ M : ℝ) (ht : 0<τ) (hM : 0≤M)
    (o : Site c) (f : Vec G c 1→ℝ)
    (h : ∀ l : Fin n→ raw G c, (marks G c τ).pay (List.ofFn l) o*|FreeResolvent.TestD.jet (ray G c) f (List.ofFn l) 0|≤M) :
    Root n (τ/2) o (fun _ : PUnit => o) (fun _ => f) ((torusPay (PAC G 1) (τ/2))^n*M) := by
  apply contract; have hf := volume c (PAC G 1) (τ/2) (half_pos ht)
  have hc (t : PUnit) (l : Fin n→ raw G c) : Real.exp ((2*(τ/2))*distance (native c) o hearth (fun _ : PUnit => o) t l)*
      |iteratedFDeriv ℝ n f 0 (ray G c ∘ l)|≤M := by
    have q := h l; change (positions (native c) hearth τ).pay _ o*_≤M at q
    rw [Stars.pays,Stars.list_result] at q
    simpa only [distance,Cost.self,zero_add,show 2*(τ/2)=τ by ring] using q
  simpa only [one_mul] using sum (native c) o (hearth (G:=G) (r:=1)) (fun _ : PUnit => o) n (τ/2) M
    (torusPay (PAC G 1) (τ/2)) 1 hM hf (single_volume (native c) o (half_pos ht).le) _ hc

/-- The sum allows a different genuine changed forest at each physical site. -/
theorem tagged (G : Gauge) (c : Side) {n : ℕ} (τ M : ℝ) (ht : 0<τ) (hM : 0≤M)
    (o : Site c) (f : Site c→Vec G c 1→ℝ)
    (h : ∀ v (l : Fin n→ raw G c), (marks G c τ).pay (List.ofFn l) o*((native c).weight τ o v*|FreeResolvent.TestD.jet (ray G c) (f v) (List.ofFn l) 0|)≤M) :
    Root n (τ/2) o id f ((torusPay PUnit (τ/2)*(torusPay (PAC G 1) (τ/2))^n)*M) := by
  apply contract; have hf := volume c (PAC G 1) (τ/2) (half_pos ht)
  have hc (v : Site c) (l : Fin n→ raw G c) : Real.exp ((2*(τ/2))*distance (native c) o hearth id v l)*
      |iteratedFDeriv ℝ n (f v) 0 (ray G c ∘ l)|≤M := by
    have q := h v l; change (positions (native c) hearth τ).pay _ o*_≤M at q
    rw [Stars.pays,Stars.list_result] at q
    simpa only [distance,id_eq,Cost.weight,show 2*(τ/2)=τ by ring,mul_add,Real.exp_add,mul_assoc,mul_left_comm] using q
  exact sum (native c) o (hearth (G:=G) (r:=1)) id n (τ/2) M (torusPay (PAC G 1) (τ/2)) (torusPay PUnit (τ/2)) hM hf
    (site_volume c (half_pos ht)) _ hc

end YM.Integration.PhysicalAffineScalarFieldContraction
end
