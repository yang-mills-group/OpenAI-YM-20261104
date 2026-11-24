import YM.Integration.WilsonIndependentCollarBinaryRead

/-! Total rooted salary of the actual two-block Wick birth. Input fronts
need not agree. Their only shared debit is the genuine covariance line. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarBinarySalary
open Finset Function Lattice Laurent Bloch Metric Precision RG Work.F08 Wilson FormalBulk08
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Winding
open WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Classical BigOperators

def split {U : Type} (i j : ℕ) (π : Equiv.Perm (Fin (i+j))) :
    ((Fin (i+j)→U) × (Fin 2→U)) ≃ ((Fin (i+1)→U) × (Fin (j+1)→U)) where
  toFun t := (Fin.cons (t.2 0) (fun z=>t.1 (π (Fin.castAdd j z))),
    Fin.cons (t.2 1) (fun z=>t.1 (π (Fin.natAdd i z))))
  invFun t := ((Fin.append (Fin.tail t.1) (Fin.tail t.2)) ∘ π.symm, ![t.1 0,t.2 0])
  left_inv := by
    rintro ⟨x,y⟩; apply Prod.ext
    · funext z
      simp only [Fin.tail_cons]
      change Fin.append (fun u=>(x∘π) (Fin.castAdd j u)) (fun v=>(x∘π) (Fin.natAdd i v)) _ = _
      rw [Fin.append_castAdd_natAdd]
      simp
    · change ![y 0,y 1]=y
      funext z; fin_cases z <;> rfl
  right_inv := by
    rintro ⟨u,v⟩; apply Prod.ext
    · change Fin.cons (u 0) (fun k=>Fin.append _ _ (π.symm (π (Fin.castAdd j k))))=u
      simp only [Equiv.symm_apply_apply,Fin.append_left,Fin.cons_self_tail]
    · change Fin.cons (v 0) (fun k=>Fin.append _ _ (π.symm (π (Fin.natAdd i k))))=v
      simp only [Equiv.symm_apply_apply,Fin.append_right,Fin.cons_self_tail]

variable {ι α : Type} [DecidableEq ι] [Fintype α]
variable {D : ι→ℕ} {S J : Finset ι} {n : Side}
local notation "U" => Site n × α
theorem original (C : ropes (Site n) α α) (σ z : ℝ) (hC : dragCup (tor n) σ z C)
    (sub : J⊆S) (X : Gen (Pen D J) U) (Y : Gen (Pen D (S\J)) U) (i j : ℕ)
    (w : (Fin (i+j)→U)→ℝ) (a : (Fin (i+1)→U)→ℝ) (b : (Fin (j+1)→U)→ℝ)
    (hw : ∀x,0≤w x) (ha : ∀x,0≤a x) (hb : ∀x,0≤b x)
    (fronts : ∀ (π:Equiv.Perm (Fin (i+j))) (x:Fin (i+j)→U) (y:Fin 2→U),
      let t := split i j π (x,y)
      w x ≤ a t.1 * b t.2 * Real.exp (σ*(tor n).gap (y 0).1 (y 1).1)) :
    ∑ x,w x*‖refuge (swivel (lakeL C sub X Y (i+j) i j)) x‖ ≤
      sealM i j*z*((∑ u,a u*‖X (i+1) u‖) * ∑ v,b v*‖Y (j+1) v‖) := by
  classical
  let K := lakeL C sub X Y (i+j) i j
  let Z := sealM i j*z
  let F (t : (Fin (i+1)→U) × (Fin (j+1)→U)) :=
    Z*((a t.1*‖X (i+1) t.1‖)*(b t.2*‖Y (j+1) t.2‖))
  have point (π:Equiv.Perm (Fin (i+j))) (x:Fin (i+j)→U) (y:Fin 2→U) :
      w x*‖K (x∘π) y‖ ≤ F (split i j π (x,y)) := by
    let t := split i j π (x,y)
    let e := Real.exp (σ*(tor n).gap (y 0).1 (y 1).1)
    have gap : e * ‖K (x∘π) y‖ ≤ Z*(‖X (i+1) t.1‖*‖Y (j+1) t.2‖) :=
      WilsonIndependentCollarFirstJoinIncome.lamp (tor n) C hC sub X Y i j (x∘π) y
    calc
      _ ≤ a t.1*b t.2*e*‖K (x∘π) y‖ :=
        mul_le_mul_of_nonneg_right (fronts π x y) (norm_nonneg _)
      _ = (a t.1*b t.2)*(e*‖K (x∘π) y‖) := by ring
      _ ≤ (a t.1*b t.2)*(Z*(‖X (i+1) t.1‖*‖Y (j+1) t.2‖)) :=
        mul_le_mul_of_nonneg_left gap (mul_nonneg (ha t.1) (hb t.2))
      _ = F t := by dsimp only [F]; ring
  have all (π:Equiv.Perm (Fin (i+j))) :
      ∑ x, w x * ∑ y, ‖K (x∘π) y‖ ≤ ∑ t,F t := by
    rw [← (split i j π).sum_comp F,Fintype.sum_prod_type]
    apply sum_le_sum; intro x _
    rw [mul_sum]
    apply sum_le_sum; intro y _
    exact point π x y
  let k := (Fintype.card (Equiv.Perm (Fin (i+j))):ℝ)
  have kp : 0<k := by dsimp [k]; positivity
  have row (x : Fin (i+j)→U) : ‖refuge (swivel K) x‖ ≤
      k⁻¹*∑ π:Equiv.Perm (Fin (i+j)), ∑ y, ‖K (x∘π) y‖ := by
    have readout : refuge (swivel K) x =
        k⁻¹ • ∑ π:Equiv.Perm (Fin (i+j)), ∑ y,K (x∘π) y := by
      simp only [refuge,swivel,k,Pi.smul_apply,Finset.sum_apply,smul_sum]
      rw [sum_comm]
    rw [readout,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr kp)]
    exact mul_le_mul_of_nonneg_left
      ((norm_sum_le ..).trans (sum_le_sum fun π _=>norm_sum_le ..)) (inv_nonneg.mpr kp.le)
  calc
    _ ≤ ∑ x, w x * (k⁻¹ * ∑ π:Equiv.Perm (Fin (i+j)), ∑ y,‖K (x∘π) y‖) :=
      sum_le_sum fun x _=>mul_le_mul_of_nonneg_left (row x) (hw x)
    _ = k⁻¹ * ∑ π:Equiv.Perm (Fin (i+j)), ∑ x,w x * ∑ y,‖K (x∘π) y‖ := by
      simp only [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl; intro π _
      apply sum_congr rfl; intro x _
      apply sum_congr rfl; intro y _
      ring
    _ ≤ k⁻¹ * ∑ _π:Equiv.Perm (Fin (i+j)), ∑ t,F t :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun π _=>all π) (inv_nonneg.mpr kp.le)
    _ = ∑ t,F t := by
      rw [sum_const,nsmul_eq_mul,card_univ]; change k⁻¹*(k*_)=_; rw [←mul_assoc,inv_mul_cancel₀ kp.ne',one_mul]
    _ = _ := by
      rw [Fintype.sum_prod_type]; simp only [F,Z,mul_sum,sum_mul]
      rw [sum_comm]

omit [DecidableEq ι] [Fintype α] in
theorem span (o w : Site n) (i j : ℕ) (π : Equiv.Perm (Fin (i+j)))
    (x : Fin (i+j)→U) (y : Fin 2→U) :
    let t := split i j π (x,y)
    max (tread (tor n) w x) ((tor n).gap o w) ≤
      tread (tor n) o t.1 + tread (tor n) w t.2 + (tor n).gap (y 0).1 (y 1).1 := by
  intro t
  let d := tor n
  have retained : tread d w x ≤ brims d w x y :=
    league_le d (stud w x) (fun s t=>leg_le d (Sum.elim (stud w x) (Prod.fst ∘ y))
      (Sum.inl s) (Sum.inl t))
  have left : soar d t.1 ≤ tread d o t.1 :=
    league_le d _ fun s u=>leg_le d (stud o t.1) s.succ u.succ
  have crown := right_cup (d:=d) (w:=w) (r:=i) (k:=j) (x∘π) y
  rw [brims_roll] at crown
  change brims d w x y ≤ soar d t.1 + d.gap (y 0).1 (y 1).1 + tread d w t.2 at crown
  have la : d.gap o (y 0).1 ≤ tread d o t.1 := leg_le d (stud o t.1) 0 (Fin.succ 0)
  have rb : d.gap (y 1).1 w ≤ tread d w t.2 := leg_le d (stud w t.2) (Fin.succ 0) 0
  have cross := d.tri o (y 0).1 w
  have last := d.tri (y 0).1 (y 1).1 w
  change max (tread d w x) (d.gap o w) ≤
    tread d o t.1 + tread d w t.2 + d.gap (y 0).1 (y 1).1
  apply max_le <;> omega

omit [Fintype α] in
/-- On the actual finite packet, the two earlier roots and every free angular
leg have a single exponential salary. Each input keeps its own original root. -/
theorem posted {G : Gauge} {I : Arch G} {Z : Finset ι} {k : ι→ℕ} {e : ℕ}
    (p : PackOne Z D k e I) (sub : J⊆S) (t q u e' i j : ℕ) (o w : Site p.V.n) :
    ∑ x,Real.exp (I.s*max (tread (tor p.V.n) w x) ((tor p.V.n).gap o w)) *
      ‖refuge (swivel (lakeL p.N sub (p.surfU J t q) (p.surfU (S\J) u e') (i+j) i j)) x‖ ≤
      sealM i j*I.mass*((∑ a,Real.exp (I.s*tread (tor p.V.n) o a) * ‖p.surfU J t q (i+1) a‖) *
        ∑ b,Real.exp (I.s*tread (tor p.V.n) w b) * ‖p.surfU (S\J) u e' (j+1) b‖) := by
  apply original p.N I.s I.mass p.V.rateRamp.bow sub _ _ i j _ _ _
    (fun x=>(Real.exp_pos _).le) (fun x=>(Real.exp_pos _).le) (fun x=>(Real.exp_pos _).le)
  intro π x y t'
  rw [←Real.exp_add,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := span o w i j π x y
  have bound : (↑(max (tread (tor p.V.n) w x) ((tor p.V.n).gap o w)):ℝ) ≤
      ↑(tread (tor p.V.n) o t'.1) + ↑(tread (tor p.V.n) w t'.2) +
        ↑((tor p.V.n).gap (y 0).1 (y 1).1) := by exact_mod_cast h
  have mul := mul_le_mul_of_nonneg_left bound I.h.le
  simpa only [Nat.cast_max,mul_add] using mul

end YM.Integration.WilsonIndependentCollarBinarySalary
