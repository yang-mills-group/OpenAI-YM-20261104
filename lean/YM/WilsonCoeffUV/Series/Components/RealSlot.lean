import Mathlib.Analysis.Normed.Module.FiniteDimension
import YM.WilsonCoeffUV.Series.Components.GermJet
import YM.WilsonCoeffUV.Series.Components.UnitFactorials
import Mathlib.Algebra.MvPolynomial.Funext

/-! Lifts of literal Taylor and coordinate pull before Wire. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue
open Matrix Function PowerSeries
open scoped Topology ContDiff BigOperators
variable {R U V W: Type*}
def shine {k:ℕ} [Zero R] (u:Ten R U k) : Gen R U:= fun i x=> if h:k=i then u (x ∘ Fin.cast h) else 0
lemma shine_lit {k:ℕ}[Zero R](u:Ten R U k) : shine u k=u := by ext i; simp [shine]
lemma shine_dark {k:ℕ}[Zero R]{u:Ten R U k}{n}(h:k≠n) : shine u n=0:= funext fun _=> dif_neg h
lemma shine_pure {k:ℕ}[Zero R]{u:Ten R U k}(h:Smooth u): Pure (shine u) := by intro i; by_cases hh:k=i; subst k; rw [shine_lit]; exact h; rw [shine_dark hh]; exact Smooth.zero
variable [Fintype U] [Fintype V] [Fintype W]
lemma visible_shine {k:ℕ}(u:Ten ℝ U k): totalR (shine u)=paint k u := by rw [totalR,finsum_eq_single _ k,shine_lit]; intro j hj; rw [shine_dark hj.symm,map_zero]

def sprig (f:Lawn U→ℝ)(k:ℕ) : ℕ → Gen ℝ U := fun e=> shine (rye f (k+e))
lemma sprig_flash (f:Lawn U→ℝ)(k:ℕ): flash (sprig f k)= PowerSeries.mk (fun i=>coeff (k+i) (jet f)) := by ext1 i; rw [flash,coeff_mk,coeff_mk,jet_apply]; exact visible_shine _
lemma moves (f:Lawn U→ℝ){k}(h:∀ i<k,coeff i (jet f)=0) : X^k*flash (sprig f k)=jet f := by
  rw [sprig_flash]; ext1 i; rw [coeff_X_pow_mul']; split <;> rename_i hx
  · rw [coeff_mk, Nat.add_sub_of_le hx];
  rw [h i (by omega)]
lemma sprig_count (f:Lawn U→ℝ)(k): shellK k (sprig f k):= fun _ _ h=> shine_dark (by omega)
lemma sprig_pure (f:Lawn U→ℝ)(hf:Green f)(k e:ℕ): Pure (sprig f k e):=shine_pure (rye_sym hf _)

omit [Fintype U] in
lemma Pure.neg {p: Gen ℝ U}(h:Pure p) : Pure (-p) := by intro i j x; simp_rw [Pi.neg_apply,h i j x]
omit [Fintype U] in
lemma Pure.add {R:Type*}[Add R]{p q:Gen R U}(h:Pure p)(e:Pure q): Pure (p+q) := fun i=> (h i).add (e i)
omit [Fintype U] in
lemma Pure.sub {p q:Gen ℝ U}(h:Pure p)(u:Pure q) : Pure (p-q):= by rw [sub_eq_add_neg]; exact h.add u.neg
omit [Fintype U] in
lemma Pure.zero {R:Type*}[Zero R]: Pure (0:Gen R U) := fun _=> Smooth.zero

def fade [AddCommGroup R] [Module ℝ R](K:Matrix U V ℝ)(P:Gen R U) : Gen R V:= fun r x=> ∑ y,(∏ i,K (y i) (x i)) • P r y
omit [Fintype V] in
lemma fade_finite [AddCommGroup R] [Module ℝ R]{P:Gen R U}(h:FiniteGen P)(K:Matrix U V ℝ): FiniteGen (fade K P) :=
    ⟨h.choose,fun i hi=> funext fun j=> by rw [fade,h.choose_spec i hi]; simp⟩
omit [Fintype V] in
lemma fade_pure [AddCommGroup R] [Module ℝ R]{P:Gen R U}(h:Pure P)(K:Matrix U V ℝ): Pure (fade K P) := by
  intro i s x; unfold fade
  conv_lhs => rw [← Equiv.sum_comp (s.symm.arrowCongr (Equiv.refl U))]
  exact Finset.sum_congr rfl fun j _=> by
    rw [show (s.symm.arrowCongr (Equiv.refl U)) j=j ∘ s from rfl, h i s j]; congr 1
    exact Fintype.prod_equiv s _ _ fun _=>rfl
omit [Fintype V] in
lemma fade_shell [AddCommGroup R][Module ℝ R](K:Matrix U V ℝ){l:ℕ}{P:ℕ→ Gen R U}(h:shellK l P) : shellK l (fun i=> fade K (P i)) := fun j r p=> funext fun i=> by change fade _ _ _ _= _; rw [fade,h j r p]; simp

def cord (K:Matrix U V ℝ) : POL U →ₐ[ℝ] POL V := MvPolynomial.aeval (fun i=> ∑ j : V,MvPolynomial.C (K i j)* MvPolynomial.X j)
omit [Fintype U] in
lemma cord_var (K:Matrix U V ℝ)(i:U) : cord K (MvPolynomial.X i)=∑ j : V,MvPolynomial.C (K i j)*MvPolynomial.X j:= MvPolynomial.aeval_X ..
lemma fade_one (K:Matrix U V ℝ)(P:Gen ℝ U)(r): paint r (fade K P r)=cord K (paint r (P r)) := by
  rw [cord, palms_scale (V:=V)]; congr 1; funext i; unfold fade; exact Finset.sum_congr rfl fun j _=> by rw [smul_eq_mul,mul_comm]
lemma fade_visible (K:Matrix U V ℝ)(P:Gen ℝ U)(h:FiniteGen P) : totalR (fade K P)=cord K (totalR P) := by
  rw [visible (P:=fade K P) (n:=h.choose) (fun i hi=> funext fun j=> by rw [fade,h.choose_spec _ hi]; simp), visible h.choose_spec, map_sum]; simp_rw [fade_one]

def loom (K:Matrix U V ℝ) : Ink U→+* Ink V:= PowerSeries.map (cord K).toRingHom
omit [Fintype U] in
lemma loom_pin (K:Matrix U V ℝ)(i:U): loom K (path i)=∑ j : V,K i j • path j := by
  rw [loom,path,map_C, show (cord _).toRingHom _ = _ from cord_var K i,map_sum]; exact Finset.sum_congr rfl fun j _=> by rw [map_mul,Algebra.smul_def,real_alg]; rfl
omit [Fintype U] in
lemma loom_real (K:Matrix U V ℝ)(u:ℝ): loom K (realS u)=realS u := by rw [show realS u=C _ from rfl,loom,map_C]; simp [cord,MvPolynomial.algebraMap_eq,realS]
omit [Fintype U] in
lemma loom_smul (K:Matrix U V ℝ)(u:ℝ)(p:Ink U) : loom K (u • p)=u • loom K p:= by rw [Algebra.smul_def,Algebra.smul_def,map_mul,real_alg,real_alg,loom_real]
lemma loom_fade (K:Matrix U V ℝ)(P:ℕ→Gen ℝ U)(h:∀ i,FiniteGen (P i)): loom K (flash P)= flash (fun i=>fade K (P i)) := by
  ext1 n; rw [flash,flash,loom,coeff_mk,coeff_map,coeff_mk,fade_visible K _ (h n)]; rfl
omit [Fintype U] in
lemma cord_apply (K:Matrix U V ℝ)(v:Lawn V)(p:POL U): MvPolynomial.eval v (cord K p) = MvPolynomial.eval (K *ᵥ v) p := by
  induction p using MvPolynomial.induction_on with
  | C r=> simp [cord,MvPolynomial.algebraMap_eq]
  | add p q a b=> simp only [map_add,a,b]
  | mul_X p j h=> rw [map_mul,map_mul,map_mul,h,cord_var,MvPolynomial.eval_X,map_sum]; simp_rw [map_mul,MvPolynomial.eval_X,MvPolynomial.eval_C]; rfl
omit [Fintype U] in
lemma loom_loom (K:Matrix U V ℝ)(J:Matrix V W ℝ): (loom J).comp (loom K)=loom (K*J) := by
  apply serial_ext (by simp [loom]) _ (by simp [loom]); intro p; induction p using MvPolynomial.induction_on with
  | C a=> change loom J (loom K (realS _))=loom (K*J) (realS _); rw [loom_real,loom_real,loom_real]
  | add p q a b=> simp_rw [map_add,a,b]
  | mul_X p j h=> simp only [map_mul,h,show C _=path j from rfl]; refine congrArg ((loom _) (C p) * ·) (show ((loom J).comp (loom K)) (path j)= loom (K*J) (path j) from ?_)
                  rw [RingHom.comp_apply, loom_pin, map_sum,loom_pin]; simp_rw [loom_smul,loom_pin,Finset.smul_sum, Matrix.mul_apply,Finset.sum_smul,smul_smul]; rw [Finset.sum_comm]

def orbQ (K:Matrix U U ℝ) : Ten ℝ U 2 := fun i=> K (i 0) (i 1)/2
omit [Fintype U] in
lemma orb_smooth (K:Matrix U U ℝ)(h:K.transpose=K): Smooth (orbQ K) := by
  intro s x
  have he:s 0≠s 1:= fun H=> zero_ne_one (s.injective H)
  generalize hx:s 0=a at *; generalize hg:s 1=b at *
  simp only [orbQ,Function.comp_apply,hx,hg]; fin_cases a <;> fin_cases b <;> simp_all
  rw [show K (x 1) (x 0)=K (x 0) (x 1) from congr_fun (congr_arg (fun M:Matrix U U ℝ=> M (x 0)) h) (x 1)]
lemma orb_paint (K:Matrix U U ℝ) : paint _ (orbQ K)=(1/2:ℝ) • (∑ i:U, ∑ j:U,K i j • (MvPolynomial.X i * MvPolynomial.X j)) := by
  rw [sprouts]; simp_rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; rw [sprouts,Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [shell _ (fun i=>i.elim0), prune,prune,orbQ]; simp only [Fin.cons_zero,Fin.cons_one, smul_smul]
  rw [Algebra.smul_def, MvPolynomial.algebraMap_eq,show (1/2:ℝ)*K i j= K i j/2 by ring]; ring
lemma orb_eval (K:Matrix U U ℝ)(a:Lawn U) : MvPolynomial.eval a (paint 2 (orbQ K))=dotProduct a (K *ᵥ a)/2 := by
  rw [orb_paint]; simp only [Algebra.smul_def,map_mul, MvPolynomial.algebraMap_eq,map_sum,MvPolynomial.eval_C,MvPolynomial.eval_X, Matrix.mulVec,dotProduct,Finset.mul_sum,div_eq_mul_inv,Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

-- utilities for direct sums

def leftArm (x:Lawn (U⊕V)) : Lawn U:= fun i=>x (.inl i)
def rightArm (x:Lawn (U⊕V)) : Lawn V:= fun i=>x (.inr i)
-- matrices selecting
variable (U V) [DecidableEq U] [DecidableEq V]
def leftFlag : Matrix U (U⊕V) ℝ := of fun i j=> if j=.inl i then 1 else 0
def rightFlag : Matrix V (U⊕V) ℝ := of fun i j=> if j=.inr i then 1 else 0
variable {U V}
lemma left_hit (p:Lawn (U⊕V)): leftFlag U V *ᵥ p = leftArm p := by ext i; unfold Matrix.mulVec dotProduct; rw [Finset.sum_eq_single (Sum.inl i)] <;> simp +contextual [leftFlag,leftArm]
lemma right_hit (p:Lawn (U⊕V)): rightFlag U V *ᵥ p = rightArm p := by ext i; unfold Matrix.mulVec dotProduct; rw [Finset.sum_eq_single (Sum.inr i)] <;> simp +contextual [rightFlag,rightArm]
lemma hold_loom : loom (rightFlag U V)=holdUp U := by
  apply serial_ext (by simp [loom]) _ (by simp [holdUp,loom]); intro i; induction i using MvPolynomial.induction_on with
  | C a=> simp only [show C _= realS _ from rfl, loom_real]; simp [realS,holdUp,holdUpPoly]
  | add p q h t=> simp_rw [map_add,h,t]
  | mul_X p j h=> rw [map_mul C,map_mul,map_mul,h,show C _=path j from rfl,up_var,loom_pin];rw [Finset.sum_eq_single (Sum.inr j)] <;> simp +contextual [rightFlag]

-- compare as smooth pull
omit [DecidableEq U] [DecidableEq V] in
lemma board (K:Matrix U V ℝ) : Green fun v=> K*ᵥ v := K.mulVecLin.toContinuousLinearMap.contDiff.contDiffAt
omit [DecidableEq U] [DecidableEq V] [Fintype U] in
lemma spool_board (K:Matrix U V ℝ) (i) : spool (fun u=> K *ᵥ u) i=loom K (path i) := by
  have h (c:ℝ)(j:V) : jet ((fun _=>c)*(fun x:Lawn V=>x j)) = X * (c • path j) := by
    rw [jet_mul (f:=fun _: Lawn V=>c) (g:=fun x:Lawn V=>x j) contDiffAt_const (show ContDiffAt ℝ ω _ _ from contDiffAt_apply ℝ ℝ j 0),jet_const,jet_arg,Algebra.smul_def,real_alg,mul_left_comm]
  apply mul_left_cancel₀ (a:=(X:Ink V)) X_ne_zero; rw [spool_raised _ (by simp),loom_pin,Finset.mul_sum];
  have he : (fun u:Lawn V=> (K*ᵥ u) i)=∑ j : V, (fun x:Lawn V=> K i j * x j) := funext fun i=> Eq.symm (Finset.sum_apply ..)
  rw [he,jet_sum _ _ (fun j _=>ContDiffAt.mul contDiffAt_const (contDiffAt_apply ℝ ℝ j _))]; exact Finset.sum_congr rfl fun i_1 _=>  h (K i i_1) i_1
omit [DecidableEq U] [DecidableEq V] [Fintype U] in
lemma spool_loom (K:Matrix U V ℝ) : train (spool (fun u=> K *ᵥ u))=loom K := by
  convert! (rail (f:=loom K) (by simp [loom]) (fun i=>loom_real K i)).symm using 1; congr 1; funext i; apply spool_board
omit [DecidableEq U] [DecidableEq V] in
lemma loom_jet (K:Matrix U V ℝ)(f:Lawn U→ℝ)(h:Green f): loom K (jet f)=jet fun u=> f (K *ᵥ u) := by rw [←spool_loom, traveling (fun u=>K*ᵥ u) (board K) (by simp) f h]; rfl
end YM.WilsonCoeffUV.Blue
