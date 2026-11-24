import YM.OPE.Compatible.Cum.Juice
/-! # freezing tail. Pay via lift. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter Set MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin
variable {E F I J R:Type}
section comb
variable {e d u:ℕ}
-- Use e+d (recursive on d)
def cue {R:Type*} (x y:R)(e d:ℕ)(i:Fin (e+d)):R:= if i.val<d then x else y
abbrev pinT (p:Fin d) : Fin (e+d):= ⟨p.val,Nat.lt_of_lt_of_le p.isLt (Nat.le_add_left ..)⟩
@[simp] lemma pin0 : pinT (e:=e) (0:Fin (d+1))=0:=rfl
@[simp] lemma cueB (x y:R)(e d:ℕ)(i:Fin d):cue x y e d (pinT i)=x:= by rw [cue, if_pos i.isLt]
@[simp] lemma cueZ (x y:R)(e:ℕ):cue x y e 0=fun _=> y:=funext fun i=>by simp [cue]
lemma cusp (x y:R)(e d:ℕ): cue x y e (d+1)= Fin.cons x (cue x y e d):=by
    ext1 i; refine Fin.cases ?_ (fun i=>?_) (n:=e+d) i
    · erw [← pin0 (e:=e) (d:=d), cueB];rfl
    rw [cue]; change (if i.val+1<d+1 then x else y)= _; simp only [Nat.add_lt_add_iff_right];rfl
@[simp] lemma pinsucc (p: Fin d): pinT (e:=e) p.succ=(pinT p).succ:=rfl
lemma Tabs (f: Fin (e+d)→R) [AddCommMonoid R](h:∀ i,d ≤ i.val→ f i=0): ∑ i:Fin (e+d),f i=∑ i:Fin d,f (pinT i):=by
    induction d with
    | zero=>rw [sum_eq_zero (fun i _=>h i (by omega))]; simp
    | succ d ih=> change ∑ i:Fin ((e+d)+1),f i=_ ;rw [Fin.sum_univ_succ,Fin.sum_univ_succ (n:=d)]; exact congr_arg _ (ih (f∘Fin.succ) fun i hi=> h i.succ (by change _ ≤ i.val+1;omega))
-- perm selecting current leg at rank d+1
abbrev wand (e d:ℕ)(i:Fin (d+1)):= Equiv.swap (0:Fin (e+(d+1))) (pinT (e:=e) i)
lemma cull (x y z:R)(p:Fin (d+1)):
   Function.update (cue x y e (d+1)) (pinT p) z=(Fin.cons z (cue x y e d) : Fin (e+d+1)→ R)∘ wand e d p:=by
      ext1 i; by_cases hp:i=pinT p
      · subst i; rw [Function.update_self,comp_apply, show (wand e d p) (pinT p)=0 from Equiv.swap_apply_right ..];rfl
      rw [Function.update_of_ne hp]; refine Fin.cases ?_ (fun j=>?_) (motive:=fun i:Fin (e+d+1)=> i ≠ pinT p → cue x y e (d+1) i=_) i hp
      · intro h; rw [comp_apply,show wand e d p 0= pinT p from Equiv.swap_apply_left ..,show cue x y e (d+1) 0=x from cueB x y e (d+1) 0]; have hz:= cueB x y e (d+1) p; rw [cusp] at hz
        obtain ⟨j,H⟩:= Fin.eq_succ_of_ne_zero h.symm; rw [H];rw [H] at hz; exact hz.symm
      intro h; rw [comp_apply,show wand e d p j.succ=j.succ from Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) h, cusp];rfl
end comb
section
variable [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][NormedAddCommGroup F] [NormedSpace ℝ F][FiniteDimensional ℝ F]
variable {e d:ℕ}(x y:F)(Z:E→L[ℝ] F)
local notation "R"=>Finset I
local notation "W"=> E→ℝ
abbrev SX (f: Tensor.T F ℝ (e+d)) (v:E):= f (cue (x+Z v) y e d)
def φx (f:Tensor.T F ℝ (e+d))(v:E)(i:Fin d)(z:E):ℝ:= f (Function.update (cue (x+Z z) y e d) (pinT i) (Z v))
omit [FiniteDimensional ℝ E][FiniteDimensional ℝ F] in
lemma awake (p:Tensor.T F ℝ (e+d))(i:E): Raise i (SX (e:=e) (d:=d) x y Z p) (∑ j:Fin d, φx x y Z p i j):=by
     intro a t; let f(j:Fin (e+d))(v:E):= cue (x+Z v) y e d j; let D(j: Fin (e+d)): E→L[ℝ] F:= if j.val<d then Z else 0; let V:=a+t • i; have ht(j:Fin (e+d)):HasFDerivAt (f j) (D j) V:=by unfold f cue D; split; exact (Z.hasFDerivAt.const_add _); exact hasFDerivAt_const ..
     let L:= fun t:ℝ=>a+t • i; have hh:HasDerivAt L i t:=by simpa only [Function.comp_def,one_smul] using! HasDerivAt.const_add a ((hasDerivAt_id' t).smul_const i)
     have he := (HasFDerivAt.multilinear_comp p ht).comp_hasDerivAt t hh; refine cast ?_ he -- avoid using congr
     rw [_root_.sum_apply]; simp only [Finset.sum_apply,ContinuousLinearMap.comp_apply]; congr 1
     rw [Tabs _ (f:=fun j=> p.toContinuousLinearMap (fun j=> f j V) j ((D j) i))]; refine Finset.sum_congr rfl fun u _=>?_ ; rw [show D (pinT u)= Z from if_pos u.isLt]; rfl
     intro j hj; rw [show D j=0 from if_neg (not_lt.mpr hj)]; simp; exact p.map_coord_zero j (update_self ..)
omit [FiniteDimensional ℝ E] in
lemma cueBond (p:Tensor.T F ℝ (e+d)): Bond (SX (e:=e) (d:=d) x y Z p):=by
     refine Bond.multiline p (fun j v=> cue (x+Z v) y e d j) ?_; intro i l; unfold cue; split; simp only [map_add]; exact (Bond.keep (l x)).add (Bond.glyph (l.comp Z.toLinearMap)); exact Bond.keep _
omit [FiniteDimensional ℝ E] in
lemma φBond (p:Tensor.T F ℝ (e+d))(i:E)(j:Fin d): Bond (φx x y Z p i j):=by
     let q(k:Fin (e+d))(v:E):=(Function.update (cue (x+Z v) y e d) (pinT j) (Z i)) k
     refine Bond.multiline p q ?_; intro k ℓ; unfold q; by_cases hp:k=pinT j
     · simp_rw [hp, Function.update_self]; exact Bond.keep _
     simp_rw [Function.update_of_ne hp]; unfold cue; split; simp only [map_add]; exact (Bond.keep (ℓ x)).add (Bond.glyph (ℓ.comp Z.toLinearMap)); exact Bond.keep _
end
end YM.OPE.Libra.Shell
