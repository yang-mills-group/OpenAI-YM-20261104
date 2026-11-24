import YM.XSpace.Lantern
import YM.Next.MAXWELL.Jets

/-!
# Umbral polynomial jets on actual cells

Center half-shift operator makes discrete co-boundary and divergence EXACTLY
of degree −1, simultaneously. Field inputs use horizon grades. Centered
central-factorial polynomials (not Newton, not face integrals).
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Litter
open Lattice Sail Maxwell Maxwell.Free Filter Function Set Further.FreeCovariance.KP Tensor
open scoped Topology ContDiff BigOperators

private def fac : ℕ → ℝ → ℝ
| 0,_ => 1
| n+1,x => x * ∏ k∈ Finset.range n,(x+ (n+1:ℕ)/ (2:ℝ) - (1+(k:ℝ)))
private lemma old_fac (n:ℕ)(x:ℝ) : fac (n+1) (x+1/2)-fac (n+1) (x-1/2)=((n+1:ℕ):ℝ)* fac n x:=by
  cases n with
  | zero=> simp [fac]; ring
  | succ n=>
    let f (k:ℕ):=x+(n+1:ℕ)/(2:ℝ)-(1+(k:ℝ))
    let a:ℝ:=(n+1:ℕ)/(2:ℝ)
    simp only [fac]
    rw [show (∏ k∈ Finset.range (n+1),(x-1/2+(n+1+1:ℕ)/ (2:ℝ)-(1+k)))=(∏ k∈ Finset.range n, f k)*(x-a) from ?_, show (∏ k∈ Finset.range (n+1),(x+1/2+(n+1+1:ℕ)/(2:ℝ)-(1+k)))=(x+a)*∏ k∈ Finset.range n,f k from ?_]
    · change _=_*(x*∏ k∈_,f k); generalize (∏ k∈ Finset.range n,f k)=Y; push_cast [a]; ring
    · nth_rw 1 [Nat.add_comm n]; rw [Finset.prod_range_add]; congr 1
      · simp [a]; ring
      refine Finset.prod_congr rfl fun k _=>?_ ; unfold f; push_cast; ring
    rw [Finset.prod_range_succ]; congr 1
    · refine Finset.prod_congr rfl fun k _=>?_; unfold f; push_cast; ring
    unfold a; push_cast; ring
private def qty {n:ℕ} (v:Fin n→Axis) (a:Axis) : ℕ := ∑ i:Fin n, if v i=a then 1 else 0
private lemma qty_sym {n:ℕ}(v:Fin n→Axis)(s:Equiv.Perm (Fin n)) : qty (v ∘ s)= qty v:=funext fun i=> Equiv.sum_comp s (fun j=> if v j=i then (1:ℕ) else 0)
private lemma qty_cons {n:ℕ}(v:Fin n→Axis)(a i:Axis) : qty (Fin.cons i v) a=(if i=a then 1 else 0)+qty v a:=by rw [qty,Fin.sum_univ_succ]; simp [qty]
private def seed (p:Axis→ℕ) (x:E4):ℝ := ∏ i:Axis,fac (p i) (x i)
def half (i:Axis):E4 := (1/2:ℝ) • basis i
lemma twice (i:Axis): half i+half i=basis i:=by unfold half; rw [← add_smul]; norm_num
private def under (p:Axis→ℕ) (i:Axis) := update p i (p i-1)
private lemma below (p:Axis→ℕ) (i:Axis) (x:E4) : seed p (x+half i) - seed p (x-half i)=(p i:ℝ)*seed (under p i) x:=by
  let s : Finset Axis:= Finset.univ \ {i}; let t:= ∏ a ∈ s, fac (p a) (x a)
  have cut (x:E4) (p) : seed p x= fac (p i) (x i) *∏ a∈s,fac (p a) (x a):=Finset.prod_eq_mul_prod_sdiff_singleton i _ (by simp)
  have ht (y:E4)(q:Axis→ℕ)(h:∀ j,j≠i→q j=p j∧ y j=x j): (∏ a∈s,fac (q a) (y a))=t:=Finset.prod_congr rfl fun a ha=>by obtain ⟨H,K⟩:=h a (by simpa [s] using ha); rw [H,K]
  rw [cut,cut,cut, ht _ p (fun _ h=>⟨rfl,by simp [half,h]⟩), ht _ p (fun _ h=>⟨rfl,by simp [half,h]⟩), ht x (under p i) (fun _ h=>⟨by simp [under,h],rfl⟩)]
  rw [← sub_mul, ← mul_assoc]; simp only [under,update_self]; congr 1
  simp [half]; cases h:p i with | zero=> simp [fac] | succ n=> simpa using old_fac n (x i)

variable {F:Type*}[NormedAddCommGroup F][NormedSpace ℝ F]{n:ℕ}
abbrev piece (n:ℕ)(F:Type*) [NormedAddCommGroup F][NormedSpace ℝ F]:=T E4 F n
def board (x:E4): piece n F →ₗ[ℝ] F where
  toFun A:= ∑ t: Fin n→Axis, seed (qty t) x • A (basis ∘ t)
  map_add' a b:=by simp [smul_add,Finset.sum_add_distrib]
  map_smul' a b:=by simp [Finset.smul_sum,smul_comm a]

private lemma blade (A:piece (n+1) F)(h:Sym A)(i:Axis)(x:E4)(j:Fin (n+1)): (∑ t:Fin (n+1)→Axis, if t j=i then seed (under (qty t) i) x • A (basis ∘ t) else 0)= board x (A.curryLeft (basis i)):=by
  let f (t:Fin (n+1)→Axis):= if t j=i then seed (under (qty t) i) x • A (basis ∘ t) else 0
  let s:=Equiv.swap j 0
  rw [← Equiv.sum_comp ((Fin.consEquiv (fun _:Fin (n+1)=>Axis)).trans (Equiv.arrowCongr s.symm (Equiv.refl Axis))) f,Fintype.sum_prod_type]
  apply Eq.trans _ (show (∑ a:Axis, if a=i then board x (A.curryLeft (basis i)) else 0)= board x _ by simp); apply Finset.sum_congr rfl; intro a _
  have he (t:Fin n→Axis) : (Equiv.arrowCongr s.symm (Equiv.refl Axis)) ((Fin.consEquiv (fun _:Fin (n+1)=>Axis)) (a,t))= (Fin.cons a t) ∘ s :=rfl
  have hs:s j=0:=Equiv.swap_apply_left ..
  simp_rw [Equiv.trans_apply,he, f,← comp_assoc,h _ s, qty_sym,comp_apply,hs,Fin.cons_zero]; split_ifs with H
  · subst a; apply Finset.sum_congr rfl; intro t _
    rw [show under (qty (Fin.cons i t)) i=qty t from funext fun k=>by by_cases H:k=i; subst k; simp [under,qty_cons]; simp [under,H,Ne.symm H,qty_cons]]
    change _ = _ • A (Fin.cons _ _); rw [show (basis ∘ Fin.cons i t)=Fin.cons (basis i) (basis ∘ t) from funext fun v=>by cases v using Fin.cases <;> rfl]
  simp
lemma plays (A:piece (n+1) F)(h:Sym A)(i:Axis)(x:E4): board (x+half i) A - board (x-half i) A= board x (((n+1:ℕ):ℝ) • (A.curryLeft (basis i))):=by
  change (∑ t:Fin (n+1)→ Axis,_) -(∑ t:Fin (n+1)→Axis,_) =_
  rw [← Finset.sum_sub_distrib]; simp_rw [← sub_smul,below,mul_smul]
  conv_lhs=> arg 2; ext t; rw [qty,Nat.cast_sum,Finset.sum_smul]
  push_cast; simp_rw [ite_smul,zero_smul,one_smul]; rw [Finset.sum_comm]; simp only [blade A h i x]; rw [map_smul]; simp; norm_cast
lemma steady (A:piece 0 F)(x:E4):board x A= diagonal A 0:=by
  unfold board; simp [seed,qty,fac]; exact congr_arg A (Subsingleton.elim ..)
-- homogenize by a spacing variable (both for the limit and for shell bounds)
private def timesF : ℕ → ℝ×ℝ → ℝ
| 0, _ => 1
| n+1, (a,x) => x* ∏ k∈ Finset.range n,(x+a*((n+1:ℕ)/(2:ℝ)-(1+(k:ℝ))))
private lemma timesF_cont (n:ℕ): Continuous (timesF n):=by cases n with
  | zero => exact continuous_const
  | succ n =>
    change Continuous fun p:ℝ×ℝ => p.2* ∏ k∈ Finset.range n,(p.2+p.1*_); fun_prop
private lemma fac_scaled (a x:ℝ)(n:ℕ): timesF n (a,a*x)=a^n*fac n x:=by
  cases n with
  | zero => simp [timesF,fac]
  | succ n=>
    simp only [fac,timesF]; rw [pow_succ]; simp_rw [← mul_add a, ← add_sub_assoc]; rw [Finset.prod_mul_distrib]; simp only [Finset.prod_const,Finset.card_range]; ring
private lemma times_zero (x:ℝ)(n:ℕ):timesF n (0,x)=x^n:=by cases n <;> simp [timesF,pow_succ', mul_comm x]
private lemma size_qty (t:Fin n→Axis): ∑ i:Axis, qty t i=n:=by
  unfold qty; rw [Finset.sum_comm]
  simp only [Fintype.sum_ite_eq]; simp
private def spring (z:ℝ×E4) (t:Fin n→Axis):ℝ:=∏ i:Axis,timesF (qty t i) (z.1,z.2 i)
private lemma spring_cont (t:Fin n→Axis): Continuous fun z:ℝ×E4=>spring z t:= continuous_finsetProd _ fun k _=>
  (timesF_cont _).comp (continuous_fst.prodMk ((EuclideanSpace.proj k (𝕜:=ℝ)).continuous.comp continuous_snd))
private lemma spring_ap (x:E4)(a:ℝ)(t:Fin n→Axis) : spring (a,a • x) t=a^n*seed (qty t) x:=by unfold spring; simp_rw [PiLp.smul_apply, smul_eq_mul, fac_scaled]; rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,size_qty];rfl
private lemma spring_zero (x:E4)(t:Fin n→Axis): spring (0,x) t=∏ k: Fin n,x (t k):=by
  unfold spring; simp_rw [times_zero]
  let s:Finset (Fin n):= Finset.univ; let f (i:Fin n):=x (t i)
  have he: (∏ i:Axis, ∏ k∈ s with t k=i, f k)=(∏ k:Fin n,f k):=by rw [Finset.prod_fiberwise_eq_prod_filter]; simp [s]
  rw [← he]; refine Finset.prod_congr rfl fun i _=>Eq.symm ?_
  apply (Finset.prod_congr rfl (g:=fun _=>x i) (fun k h=>congr_arg (fun i:Axis=>x i) (Finset.mem_filter.mp h).2)).trans
  simp [s,qty]

def slope (A:piece n F) (z:ℝ×E4):F:= ∑ t:Fin n→Axis,spring z t • A (basis∘t)
lemma slope_cont : Continuous fun y:piece n F × (ℝ×E4) => slope y.1 y.2:=by
  unfold slope; apply continuous_finsetSum _; intro t _; exact ((spring_cont t).comp continuous_snd).smul ((ContinuousMultilinearMap.apply ℝ (fun _:Fin n=>E4) F (basis∘t)).continuous.comp continuous_fst)
lemma slope_ap (A:piece n F) (x:E4) (a:ℝ): slope A (a,a • x)=(a^n) • board x A:=by unfold slope; simp_rw [spring_ap,mul_smul,← Finset.smul_sum];rfl
lemma dirs (x:E4): (∑ i : Axis,x i • basis i)=x:=by ext k; simp
lemma slope_zero (A:piece n F)(x:E4): slope A (0,x)=diagonal A x:=by
  unfold slope; simp_rw [spring_zero]; unfold Tensor.diagonal; conv_rhs=> arg 2; ext j; rw [← dirs x]
  rw [A.map_sum]; exact Finset.sum_congr rfl fun i _=> (A.map_smul_univ (x ∘ i) (basis ∘ i)).symm
lemma slopes {ι:Type*}{L:Filter ι}{v:ι→piece n F}{A:piece n F}(h:Tendsto v L (𝓝 A)) {x:ι→E4}{a:ι→ℝ}{w:E4}(ht:Tendsto (fun i=> a i • x i) L (𝓝 w))(hh:Tendsto a L (𝓝 0)): Tendsto (fun i=> ((a i)^n) • board (x i) (v i)) L (𝓝 (diagonal A w)):=by 
  rw [← slope_zero]; let J:=slope_cont.continuousAt.tendsto.comp (h.prodMk_nhds (hh.prodMk_nhds ht))
  exact J.congr (fun i=> slope_ap (v i) _ _)

lemma off_meter (n:ℕ): ∃ C:ℝ,0<C∧ ∀ (A:piece n F)(x:E4), ‖board x A‖ ≤ C*‖A‖*(1+‖x‖)^n:=by
  let s:= Icc (0:ℝ) 1 ×ˢ Metric.closedBall (0:E4) 1
  choose B h using fun (t:Fin n→Axis) => ((isCompact_Icc.prod (isCompact_closedBall (0:E4) 1)).bddAbove_image (K:=s) (spring_cont t).abs.continuousOn)
  let C:= ∑ t:Fin n→Axis, |B t|
  have hp:0≤C:= Finset.sum_nonneg fun _ _=> abs_nonneg _
  refine ⟨C+1,by positivity,fun A x=> ?_⟩; let q:ℝ:=1+‖x‖; let a:=q⁻¹; have hq:0<q:=by unfold q; positivity
  have ha:0<a:=by unfold a; positivity
  let z:ℝ×E4 := (a,a • x); have hz : z∈s:=by
    refine ⟨⟨ha.le,?_⟩,?_⟩
    · show q⁻¹ ≤ 1; rw [inv_le_one₀ hq]; exact le_add_of_nonneg_right (norm_nonneg _)
    change a • x∈ Metric.closedBall _ _; rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg ha.le, show a=q⁻¹ from rfl,mul_comm,← div_eq_mul_inv, div_le_one hq]; exact le_add_of_nonneg_left zero_le_one
  have he : ‖slope A z‖ ≤ C*‖A‖:= by
    apply (norm_sum_le ..).trans; unfold C; rw [Finset.sum_mul]; refine Finset.sum_le_sum fun i _=>?_
    rw [norm_smul]; apply mul_le_mul ((h i (show |spring z i| ∈ (fun z=> |spring z i|) '' s from mem_image_of_mem _ hz)).trans (le_abs_self _)) _ (norm_nonneg _) (abs_nonneg _)
    simpa [comp] using A.le_opNorm (basis ∘ i)
  rw [show slope A z=_ from slope_ap A x a,norm_smul,Real.norm_of_nonneg (pow_nonneg ha.le _),show a^n=(q^n)⁻¹ by rw [show a=q⁻¹ from rfl,inv_pow],mul_comm, ← div_eq_mul_inv] at he
  apply ((div_le_iff₀ (pow_pos hq n)).mp he).trans; unfold q at *; gcongr; simp
end YM.XSpace.Litter
