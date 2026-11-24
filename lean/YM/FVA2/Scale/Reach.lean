import YM.FVA2.Scale.Turn
/-!
# Dilation of fields, budgets and formal frames
Operations of the geometric action: conjugate by `Dial`, never project any
actual coefficient requests from one sphere to another. Require H-equivariance, not
rotation invariance.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Scale
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Level
variable {G:Gauge}{d j i k v:ℕ}
local notation "L"=> FieldEnd G d
local notation "S"=> Sec G d
local notation "D"=> Level.E d
local notation "r"=> Guard G d
namespace Level
variable (t v:ℝ)
lemma Dial_leaf : Dial d t (leaf G d)= leaf G d:= by
    conv_lhs=>arg 2; rw [← leaf_0 ];
    rw [taken,leaf_0]; simp [Extent.token]
lemma Dial_band : Band (Dial (G:=G) d t):= by
    intro j hj p hp; rw [Dial,LinearMap.sum_apply, AddSubmonoidClass.coe_finsetSum]; apply Submodule.sum_mem; intro i _; exact Submodule.smul_mem _ _ (remains i _ hj _ hp)
lemma Dial_ori (s:Ortho)(p:Sec G d): Dial d t (ori s d p)=ori s d (Dial d t p):= by unfold Dial; rw [LinearMap.sum_apply,LinearMap.sum_apply,map_sum]; simp only [LinearMap.smul_apply,map_smul, orient ]
lemma Dial_real (p:Sec G d): Dial d t (reel d p)=reel d (Dial d t p):= by unfold Dial; rw [LinearMap.sum_apply,LinearMap.sum_apply,map_sum]; simp_rw [LinearMap.smul_apply,(reel d).map_smulₛₗ, real ]; simp [Extent.token,-Complex.ofReal_exp]
def turner (t:ℝ): FieldEnd G d→ₗ[ℂ] FieldEnd G d where
    toFun A:= Dial d (-t)*A*Dial d t
    map_add' a b:= by rw [mul_add, add_mul]
    map_smul' c a:= by rw [mul_smul_comm,smul_mul_assoc]; rfl
lemma turn_change (A:FieldEnd G d)(h:A∈ Normalize.Change G d): turner t A∈ Normalize.Change G d:= by
    rw [may_change]; unfold turner; simp only [LinearMap.coe_mk,AddHom.coe_mk,Module.End.mul_apply]; exact ⟨ by rw [Dial_leaf, h.1,map_zero],fun i hi p hp=> Dial_band ( -t ) _ hi _ (h.2.1 _ hi _ ( Dial_band t _ hi _ hp ) ), fun p=> by rw [ Dial_real,h.2.2.1,Dial_real ],fun s p=> by rw [ Dial_ori,h.2.2.2,Dial_ori ] ⟩
lemma passed (A:FieldEnd G d)(h:Graded A): turner t A=A:= by change Dial d (-t)*A*Dial d t=_; rw [rise _ _ h,mul_assoc,spring,mul_one]
lemma turn_one : turner (d:=d) t (1:L)=1:= by change Level.Dial _ _ * 1 * _=_; rw [mul_one,spring]
lemma transfer (A:FieldEnd G d): A*Level.Dial d t=Level.Dial d t * turner t A:= by change _=_*(_*A*_); rw [←mul_assoc,←mul_assoc,autumn, one_mul]
lemma turn_mul (A B:FieldEnd G d): turner t (A*B)=turner t A * turner t B:= by
    change Level.Dial d (-t)*(A*B)*Level.Dial d t=(Level.Dial d (-t)*A*Level.Dial d t)*(Level.Dial d (-t)*B*Level.Dial d t); nth_rw 1 [← mul_one A, ← Level.autumn t ]; -- need middle Dial t * Dial -t; wrong switch
    noncomm_ring
lemma chain (h:d≤k)(p:Sec G d): Dial k t ( up h p ) = up h ( Dial d t p ):= by rw [ ← all_sig p,map_sum,map_sum,map_sum,map_sum ]; apply Finset.sum_congr rfl; intro i _; simp only [_root_.map_smul, lift_sig, exact₀ ]
end Level
variable (t v:ℝ) (A B: Guard G d)
abbrev convertT (t:ℝ)(A:Guard G d): Guard G d:= PowerSeries.mk (fun i=> Level.turner t (coeff i A))
lemma converts (h:Base A): Base (convertT t A):= by
    refine ⟨ ?_,fun i hi=>?_ ⟩; · rw [ ← coeff_zero_eq_constantCoeff_apply, convertT,coeff_mk,h.zero,turn_one]
    rw [convertT,coeff_mk]; exact turn_change t _ (h.high i hi)
lemma old_g (h:Native A): convertT t A=A:= PowerSeries.ext fun i=> ( coeff_mk .. ).trans (Level.passed t _ (h i))
lemma commuting : convertT t (A*B)= convertT t A* convertT t B:= by refine PowerSeries.ext fun i=>?_ ; rw [coeff_mul]; simp_rw [convertT, coeff_mk, coeff_mul, map_sum, Level.turn_mul]
namespace Frame
open Reg.Point
lemma step_mul (q:Cn)(h:Rooted q) : stepV q (A*B) = stepV q A*stepV q B:= by
    have H(p:Sec G d)(i:Dime G d) : tax ( stepV q (A*B) ) p i=tax ( stepV q A* stepV q B ) p i := by
        simp_rw [ horizon (q:=q) _ _ _ h,taxes,horizon (q:=q) _ _ _ h ]; rw [ ← coe_substAlgHom (Reg.Choice.licence q h), map_sum ]; simp only [map_mul, coe_substAlgHom ]
    apply PowerSeries.ext; intro i; ext1 p; apply (dime G d).repr.injective; ext1 j; replace H:= congr_arg (coeff i) (H p j); simp only [tax,coeff_mk] at H; exact H
lemma step_one (q:Cn): stepV q (1:Guard G d)=1:= by
    apply PowerSeries.ext; intro n; rw [stepV, coeff_mk ]; by_cases hp:n=0; · subst n; rw [pay0]
    rw [rules, coeff_one,if_neg hp]; apply Finset.sum_eq_zero; intro i _; rw [coeff_one]; split_ifs with he; · subst i; simp [cut,hp];
    exact smul_zero _
lemma step_mirror (h:Base A) (q:Cn)(hq:Rooted q)(hr:Reg.Unique.CoreR q) : stepV q ( mirror A )= mirror (stepV q A) := Eq.symm ( ( h.switch hr ).alone ( by rw [← step_mul _ _ _ hq,h.turn',step_one ] ) )
lemma step_identity : stepV X A = A:= by
    apply PowerSeries.ext; intro n; rw [stepV,coeff_mk,rules, Finset.sum_eq_single n ]; · simp [cut,coeff_X_pow]
    · intro i _ hi; simp [cut,coeff_X_pow, Ne.symm hi]
    simp
lemma step_repeat (q w:Cn)(hq:Rooted q)(hw:Rooted w): stepV w (stepV q A) = stepV (q.subst w) A:= by
    -- via tax & scalar
    let P:= stepV w (stepV q A); let Q:= stepV (q.subst w) A; have h : ∀ v:Sec G d,∀ i:Dime G d,tax P v i=tax Q v i:= by
       intro v i; unfold P Q; rw [ Reg.Point.horizon _ _ _ _ hw, Reg.Point.horizon _ _ _ _ hq, Reg.Point.horizon _ _ _ _ (circle q w hq hw), subst_comp_subst_apply (Reg.Choice.licence q hq) (Reg.Choice.licence w hw)]
    apply PowerSeries.ext; intro k; ext1 p; apply (dime G d).repr.injective; ext1 i; replace h:=congr_arg (coeff k) (h p i); simp only [tax,coeff_mk] at h; exact h
lemma turn_repeat : convertT v ( convertT t A )= convertT (t+v) A:= by
    apply PowerSeries.ext; intro j; simp only [convertT, coeff_mk,turner,LinearMap.coe_mk,AddHom.coe_mk]; rw [ ← Level.group, neg_add, add_comm (-t), ← Level.group ]; noncomm_ring
lemma convert_step (q:Cn): stepV q ( convertT t A ) = convertT t (stepV q A):= by
    apply PowerSeries.ext; intro i; simp_rw [stepV, convertT,coeff_mk,rules,map_sum, _root_.map_smul]
-- inheritance (arbitrary comparison intervals). terminology
end Frame
variable {t} {n:ℕ}
abbrev Walk (t:d≤k) (F:Guard G d) (A:Guard G k): Prop:=∀ i (p:Sec G d), coeff i A (up t p)=up t (coeff i F p)
namespace Walk
variable (t:ℝ){h:d≤k} {C D':Guard G d} {c d': Guard G k}
lemma mul (H: Walk h C c)(K:Walk h D' d') : Walk h (C*D') (c*d'):= by intro i p; simp only [ coeff_mul, LinearMap.sum_apply, Module.End.mul_apply,K,H,map_sum ]
lemma rewind (H: Walk h C c)(_ht: Base c)(_he: Base C): Walk h (mirror C) (mirror c):= by
    intro i; induction i using Nat.strong_induction_on with
    | _ i ih=> -- inverse coeff by invOfUnit recursion
      intro p; unfold mirror; rw [coeff_invOfUnit i c 1, coeff_invOfUnit i C 1]; simp only [ inv_one, Units.val_one ]; split_ifs with h₀; · rfl
      let Y (j:ℕ×ℕ) : FieldEnd G k:= if j.2 < i then (coeff j.1 c) * (coeff j.2 (mirror c)) else 0; let y (j:ℕ×ℕ): L:= if j.2 < i then coeff j.1 C * (coeff j.2 (mirror C)) else 0; change ((-1: FieldEnd G k)* ∑ j∈ Finset.antidiagonal i,Y j) (_)= up h (((-1:L)*∑ j∈ Finset.antidiagonal i,y j) p)

      rw [Module.End.mul_apply, Module.End.mul_apply, LinearMap.neg_apply, LinearMap.neg_apply, Module.End.one_apply, Module.End.one_apply, map_neg, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]; congr 1; refine Finset.sum_congr rfl (fun j _=>?_ ); unfold Y y; split_ifs with hv; swap; · exact ( (up h (G:=G)).map_zero ).symm
      change coeff j.1 c (coeff j.2 (mirror c) (up h p))=up h ( coeff j.1 C (coeff j.2 (mirror C) p) ); rw [ih j.2 hv,H]; -- induction

lemma steps (H:Walk h C c) (q:Cn): Walk h (Reg.Point.stepV q C) (Reg.Point.stepV q c):= by intro i p; simp_rw [ Reg.Point.stepV, coeff_mk,rules,LinearMap.sum_apply,map_sum,LinearMap.smul_apply, _root_.map_smul,H ]
lemma dial (H:Walk h C c): Walk h ( convertT t C ) (convertT t c):= by intro i p;  simp only [convertT, coeff_mk,turner,LinearMap.coe_mk,AddHom.coe_mk,Module.End.mul_apply]; rw [Level.chain,H, Level.chain]
lemma slot (a:Toon G d) (p:Sec G d) (h:d≤k): Level.proj (Dframe.enroll h a).1 ( up h p )=up h (Level.proj a.1 p):=rfl
lemma grades (H:Walk h C c): Walk h ( diagonal C ) (diagonal c):= by
    intro i p; simp only [diagonal,coeff_mk]; rw [ ← all_sig p ]; simp only [map_sum,_root_.map_smul,lift_sig]; apply Finset.sum_congr rfl; intro j _; congr 1; rw [ ← Level.top j, ← Level.top ( Dframe.enroll h j ),Level.diagonals,Level.diagonals, Level.top, Level.top, ← lift_sig, H, slot ]; -- need check rhs simplification up_lift on diag? 
end Walk
end YM.FVA2.Scale
