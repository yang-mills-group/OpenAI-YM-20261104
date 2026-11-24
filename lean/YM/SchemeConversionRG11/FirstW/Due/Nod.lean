import YM.SchemeConversionRG11.FirstW.Due.Lodge
/-! Polar coefficient currency. Symmetries claimed only where justified. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter MeasureTheory Lattice Pert Align Topology Deck Maxwell MvPolynomial LinearMap
open scoped BigOperators Classical
variable {G : Gauge} {d : ℕ}
abbrev Dot (G : Gauge) (d : ℕ) := Who G d → ℝ
def salute (d : ℕ) : Labels.Jet G→ₗ[ℝ] Dot G d := LinearMap.pi fun i=> (Labels.axes G i.val.1).coord i.val.2 ∘ₗ LinearMap.proj i.val.1
def bark (x : Dot G d) : Labels.Jet G := fun i:ℕ=> if h:i≤d then ∑ j, x ⟨⟨i,j⟩,h⟩ • (Labels.axes G i j) else 0
def barks (d : ℕ) : Dot G d→ₗ[ℝ] Labels.Jet G where
 toFun:=bark
 map_add' a b:=by funext i; unfold bark; rw [Pi.add_apply]; split_ifs <;> simp [add_smul, Finset.sum_add_distrib]
 map_smul' a x:=by funext i; unfold bark; rw [Pi.smul_apply]; split_ifs <;> simp [Finset.smul_sum,smul_smul]
lemma bark_in (x : Dot G d) : salute d (barks d x)=x := by
 funext i; rcases i with ⟨⟨a,b⟩,h⟩; change (Labels.axes G a).repr (bark x a) b = x _; simp [bark,h, Finsupp.single_apply]
lemma bark_again (x : Labels.Jet G) (i : ℕ) (hi:i≤d) : barks d (salute d x) i=x i:=by
 change bark (salute d x) i=_; unfold bark; rw [dif_pos hi]; exact (Labels.axes G i).sum_repr (x i)
section smooth
variable {I : Type*} [Fintype I]
def look (x : I→ℝ) : Cache I→ₐ[ℂ] ℂ:=aeval fun i:I=>(↑(x i):ℂ)
def windPrice (u : I→ℝ) : Module.End ℂ (Cache I) := ∑ i:I, ((u i:ℝ):ℂ) • (pderiv i).toLinearMap
lemma wind_val (u : I→ℝ) (p : Cache I) : windPrice u p = ∑ i:I, C ((u i:ℝ):ℂ)*D1 i p:= by simp only [windPrice,LinearMap.sum_apply,LinearMap.smul_apply, Derivation.coeFn_coe,C_mul']
lemma swish (p q : Cache I) (u : I→ℝ) : windPrice u (p*q) = windPrice u p *q+p*windPrice u q := by
 rw [wind_val,wind_val,wind_val];simp only [D1,pderiv_mul,mul_add, Finset.sum_add_distrib,Finset.mul_sum, Finset.sum_mul,mul_left_comm,mul_assoc]
lemma wind_X (i : I) (u : I→ℝ) : windPrice u (X i)= C ((u i:ℝ):ℂ) := by
 rw [wind_val,Finset.sum_eq_single_of_mem i (Finset.mem_univ i)];simp;intro j _ hj; rw [D1,pderiv_X_of_ne (Ne.symm hj),mul_zero]
lemma wind_look (p:Cache I) (u x:I→ℝ) : HasDerivAt (fun t:ℝ=>look (x+t • u) p) (look x (windPrice u p)) 0 := by
 induction p using MvPolynomial.induction_on with
 | C c=>simp [wind_val,look]; exact hasDerivAt_const _ c
 | add p q he hp=>simpa only [map_add] using! he.add hp --  using he.add hp
 | mul_X p i ih=>
    have hh:HasDerivAt (fun t:ℝ=>x i+t*u i) (u i) 0:=by simpa only [one_mul] using ((hasDerivAt_id' (0:ℝ)).mul_const (u i)).const_add (x i)
    have he:HasDerivAt (fun t:ℝ=>look (x+t •u) (X i)) (u i:ℂ) 0 := by
      have H:= ((Complex.ofRealCLM.hasFDerivAt (x:=x i+(0:ℝ)*u i))).comp_hasDerivAt 0 hh; simp only [look, aeval_X]; exact H
    rw [swish,wind_X]; simp only [map_mul,map_add,look,aeval_C]; have H:=ih.mul he; simpa [look,mul_comm] using! H -- reduce def
lemma strikes (p q : Cache I) (L : Module.End ℝ (I→ℝ)) (u : I→ℝ) (he : ∀ x,look x p=look (L x) q) (x : I→ℝ) :
    look x (windPrice u p)= look (L x) (windPrice (L u) q) := by
  have hp:= wind_look p u x; simp_rw [he,map_add,map_smul] at hp; exact hp.unique (wind_look ..)
def accord (L : Module.End ℝ (I→ℝ)) (i j : I) : ℝ := L (Pi.single j 1) i
lemma second_turn (p q : Cache I) (L : Module.End ℝ (I→ℝ)) (he : ∀ x,look x p= look (L x) q) (i j:I) :
 loot p i j=∑ a:I,∑ b:I, loot q a b * (accord L a i * accord L b j :ℝ) := by
  let S(r:I):I→ℝ:=Pi.single r 1; have h := strikes (windPrice (S i) p) (windPrice (L (S i)) q) L (S j) (strikes p q L (S i) he) 0 -- syntax
  have hh (k : I) (p : Cache I): windPrice (S k) p=D1 k p:=by rw [wind_val,Finset.sum_eq_single_of_mem k (Finset.mem_univ k)]; simp [S]; intro j _ hj; simp [S,hj]
  rw [hh,hh,map_zero] at h
  have hx(p:Cache I): look (0:I→ℝ) p=coeff 0 p:= by exact aeval_zero' p
  rw [hx] at h; change _=_; rw [loot,h,wind_val (L (S i)),map_sum]; simp only [wind_val,D1,pderiv_C_mul,hx,MvPolynomial.coeff_sum,coeff_C_mul]; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; unfold loot D1; simp only [Complex.ofReal_mul, accord]; unfold S; ring
lemma third_turn (p q : Cache I) (L : Module.End ℝ (I→ℝ)) (he : ∀ x,look x p=look (L x) q) (i j k:I) :
 root3 p i j k= ∑ a:I,∑ b:I, ∑ c:I, root3 q a b c * (accord L a i * accord L b j * accord L c k :ℝ) := by
  let U : I → ℝ := Pi.single i (1:ℝ)
  have ht : windPrice U p=D1 i p := by rw [wind_val,Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]; simp [U]; intro j _ hj; simp [U,hj]
  have h:=second_turn _ _ L (strikes p q L U he) j k
  change loot (D1 i p) j k=_; rw [←ht,h,wind_val]
  simp_rw [loot,D1,map_sum, pderiv_C_mul, MvPolynomial.coeff_sum, coeff_C_mul, Finset.sum_mul]; conv_lhs=> arg 2; intro u; rw [Finset.sum_comm]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _; apply Finset.sum_congr rfl; intro z _; unfold root3 D1; unfold U accord; push_cast; ring -- U local not def
end smooth
abbrev applyJet (G : Gauge) := (i:ℕ)→ Module.End ℝ (Labels.Taylor G i)
def lit (d : ℕ) (L : applyJet G) : Module.End ℝ (Dot G d) := salute d ∘ₗ (LinearMap.pi (fun i => L i ∘ₗ LinearMap.proj i) ∘ₗ barks d)
lemma lit_any (L : applyJet G) (x : Labels.Jet G) (d : ℕ) : lit d L (salute d x) = salute d (fun i=>L i (x i)) := funext fun i=> by change (Labels.axes _ _).coord _ (L i.val.1 (barks d (salute d x) i.val.1))=_; rw [bark_again x _ i.property];rfl -- salute unfolded
lemma salute_read (q : Part G d) (x : Labels.Jet G): look (salute d x) q= Labels.read x (uncap q) := by
 induction q using MvPolynomial.induction_on with | C c=>simp [look,Labels.read,uncap] | add p q he hp=>simp only [uncap,map_add] at *;rw [he,hp] | mul_X p a he=> unfold uncap at *; rw [map_mul,map_mul,map_mul,MvPolynomial.rename_X,he]; simp [look,Labels.read,Labels.coord,salute] -- aeval
lemma seen (F : Labels.Frames G) (p:Position.E F d)(x : Labels.Jet G) : look (salute d x) (cloak F p)=Labels.read x (Full.sections _ _ p) := by rw [salute_read,stretch]
end YM.RG11.FirstW
