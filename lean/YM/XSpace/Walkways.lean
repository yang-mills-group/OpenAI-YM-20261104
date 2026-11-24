import YM.XSpace.Lantern

/-!
# Lattice power summation and massless *first* potential difference line

Riemann costs to use later. Sharper decay of first differences across seam not needed at order
one (power/c.C estimates for cubic with gauge invariant external lines use ℓ² & sup separately).
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Sail
open Filter Set Function Lattice Bloch Laurent Complex MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {n:Side}
lemma carry_at (i j:ℕ) : carry i j≤1:=by unfold carry; apply pow_le_one₀ (by positivity); apply inv_le_one_of_one_le₀; simp
lemma carry_mono (k:ℕ) {i j:ℕ} (h:i≤j): carry k j ≤ carry k i:=by unfold carry; gcongr
lemma carry_weight (v:ℕ){i j:ℕ}(h:i≤j): carry j v≤carry i v:=by unfold carry; exact pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ (by simp)) h
lemma carry_power (k r v:ℕ): carry k v * carry r v= carry (k+r) v:= (pow_add ..).symm
lemma box_rate (k:ℕ)(x:Cover): x∈box k↔reach x≤k:=by
  rw [box_test]; refine ⟨fun h=> ?_,fun h=>?_⟩; apply Finset.sup_le; intro i _; have hx:=h.1 i; have hy:=h.2 i; omega
  constructor <;> intro i <;> (have hx:= reach_at x i; omega)
def shell (r:ℕ): Finset Cover:= (box r).filter fun x=> reach x=r
lemma shell_rate (r:ℕ)(x:Cover): x∈shell r↔reach x=r:=by unfold shell; simp only [Finset.mem_filter,box_rate]; omega
lemma volume_box (r:ℕ): (box r).card=(2*r+1)^4:=by rw [Pressure.box_length,Lattice.card_layers]
lemma volume_ring (r:ℕ): (shell r).card ≤ 128*(1+r)^3:=by
  cases r with
  | zero=> apply le_trans (Finset.card_le_card (Finset.filter_subset _ (box 0))) _; rw [volume_box]; norm_num
  | succ r=>
    have he:shell (r+1)=box (r+1)\box r:=Finset.ext fun i=>by rw [shell_rate,Finset.mem_sdiff,box_rate,box_rate]; omega
    rw [he,Finset.card_sdiff_of_subset (s:=box r) (t:=box (r+1)) (fun i h=> (box_rate ..).2 (le_trans ((box_rate ..).1 h) (by omega))),volume_box,volume_box, Nat.sub_le_iff_le_add]; ring_nf; omega
lemma sum_shell {E:Type*}[AddCommMonoid E] (r:ℕ)(p:Cover→E): ∑ i∈box r,p i=∑ k∈Finset.range (r+1),∑ i∈shell k,p i:=by
  classical
  rw [← Finset.sum_biUnion]; congr 1; ext x; simp_rw [Finset.mem_biUnion,Finset.mem_range,box_rate,shell_rate]; simp
  rintro x _ y _ he; apply Finset.disjoint_left.mpr; intro i hx hy; exact he (((shell_rate ..).1 hx).symm.trans ((shell_rate ..).1 hy))
lemma carry_sum {k:ℕ}(h:4<k): Summable (fun x:Cover=>carry k (reach x)):=by
  set g:=fun i:ℕ=> 128*carry 2 i
  have hp : ∀ i,0≤ g i:=fun i=> mul_nonneg (by norm_num) (carry_pos ..).le
  have hh : Summable g:= by
    apply Summable.mul_left; unfold carry; simp_rw [inv_pow]
    have hh := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (show 1< (2:ℕ) by norm_num))
    simpa [one_div,add_comm (1:ℝ)] using hh
  refine summable_of_sum_le (c:=∑' i,g i) (fun x=> (carry_pos ..).le) fun w=>?_
  let r:= w.sup reach
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t:=box r) (fun x h=>(box_rate ..).2 (Finset.le_sup h)) (fun i _ _=> (carry_pos ..).le)) ?_
  rw [sum_shell]; apply le_trans _ (Summable.sum_le_tsum (Finset.range (r+1)) (fun i _=>hp i) hh); apply Finset.sum_le_sum; intro i _
  calc _ ≤ ∑ _x∈shell i, carry 5 i := Finset.sum_le_sum fun x hx=> by rw [(shell_rate ..).1 hx]; apply carry_weight; omega
       _ ≤ _ := ?_
  have ht : ((shell i).card:ℝ)≤128*(1+i)^3:=by exact_mod_cast volume_ring i
  rw [Finset.sum_const,nsmul_eq_mul]
  apply (mul_le_mul_of_nonneg_right ht (carry_pos ..).le).trans_eq; unfold g carry; have hi : 0<(1+(i:ℝ)):=by positivity
  field_simp

-- All periods first cost
abbrev gd := Potential.G
lemma shade (f:Site n→ℝ) (i:Axis): (∑ p, f p * (f p-f (p+step i)+(f p-f (p-step i))))=∑ p, (Δf i f p)^2:=by
  have hh (p:Site n) : f p*(f p-f (p+step i)+(f p-f (p-step i)))= f p*(f p-f (p+step i))+ f p*(f p-f (p-step i)):= mul_add ..
  simp_rw [hh,Finset.sum_add_distrib]; rw [← Equiv.sum_comp (Equiv.addRight (step i)) (fun p=> f p*(f p-f (p-step i))), ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro p _; unfold Δf; simp only [Equiv.coe_addRight,add_sub_cancel_right]; ring
lemma period_dirichlet (n:Side): (∑ i:Axis,∑ p, (Δf i (gd n) p)^2)=gd n 0-(n.val:ℝ)⁻¹^4*∑ x,gd n x:=by
  have he : ∀ p:Site n,Potential.scalar (gd n) p=(if p=0 then 1 else 0)-(n.val:ℝ)⁻¹^4:=fun p=>by rw [inv_pow]; exact Potential.poisson _
  simp_rw [← shade]; rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum, ← Potential.scalar_at, he, mul_sub, Finset.sum_sub_distrib]; simp [mul_ite,Finset.mul_sum,mul_comm]
lemma general_period_bound : ∃ C:ℝ,0<C∧∀ n:Side,∀ p:Site n,|gd n p|≤C:=by
  obtain ⟨C,hC,H⟩:= seam []; refine ⟨C*(1+1),by positivity,fun n x=>(H n x).trans ?_⟩; apply mul_le_mul_of_nonneg_left (add_le_add (carry_at ..) _) hC.le; apply inv_le_one_of_one_le₀; exact_mod_cast n.pos
lemma ℓ2_period : ∃ C:ℝ,0<C∧∀ n:Side,∀ i:Axis,(∑ p:Site n,(Δf i (gd n) p)^2) ≤ C:=by
  obtain ⟨C,hC,H⟩:= general_period_bound; refine ⟨C+C,by positivity,fun n i => ?_⟩
  apply (Finset.single_le_sum (s:=Finset.univ) (f:=fun i=> ∑ p, (Δf i (gd n) p)^2) (fun _ _=> Finset.sum_nonneg fun _ _=> sq_nonneg _) (Finset.mem_univ i)).trans
  rw [period_dirichlet, sub_eq_add_neg, ← mul_neg,← Finset.sum_neg_distrib]; apply add_le_add ((le_abs_self _).trans (H ..)); conv_rhs=>rw [← show (n.val:ℝ)⁻¹^4*∑ _p:Site n,C=C from by simp]
  · apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _=>(neg_le_abs _).trans (H n x)); positivity
lemma ℓ2_cover (i:Axis): Summable fun x: Cover=> (Δf i cover x)^2 :=by
  obtain ⟨C,hC,H⟩:= covers_decays [i]
  refine Summable.of_nonneg_of_le (fun _=>sq_nonneg _) ?_ ((carry_sum (k:=6) (by norm_num)).mul_left (C^2)); intro x
  rw [show carry 6 (reach x)= (carry 3 (reach x))^2 from Eq.symm (by rw [pow_two, carry_power]), ← mul_pow, sq_le_sq,abs_of_pos (mul_pos hC (carry_pos ..))]; exact H _
end YM.XSpace.Sail
