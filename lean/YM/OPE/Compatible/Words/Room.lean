import YM.OPE.Compatible.Words.Knot
/-! # Gaussian sifts -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt
open MeasureTheory Function Finset Filter Module
open scoped Topology BigOperators Classical ContDiff
variable {E F:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
abbrev Pole (E:Type*)[NormedAddCommGroup E][NormedSpace ℝ E](i:ℕ):= Tensor.T E ℝ i
abbrev Song (E:Type*)[NormedAddCommGroup E][NormedSpace ℝ E]:= (k:ℕ)→Pole E k
def harmon (E:Type*)[NormedAddCommGroup E][NormedSpace ℝ E](d:ℕ) : Submodule ℝ (Song E) where
    carrier:= setOf fun p=> (∀ i:ℕ,i>d→p i=0)∧∀ i:ℕ, Tensor.Sym (p i)
    zero_mem':=⟨fun _ _=>rfl,fun _ _ _=>rfl⟩
    add_mem':=fun {p q} ⟨h,hp⟩ ⟨he,hq⟩=>⟨fun k hk=>by change p k+q k= _; rw [h k hk,he k hk,zero_add],fun k u _=> by rw [Pi.add_apply,_root_.add_apply, hp .., hq k u _,_root_.add_apply] ⟩ -- hp underscores? 
    smul_mem':=fun c p ⟨h,hp⟩=>⟨fun k hk=>by change c • p k=_; rw [h k hk,smul_zero],fun k u v=>by rw [Pi.smul_apply,_root_.smul_apply, hp k u _,_root_.smul_apply] ⟩
variable {I J:Type}[Fintype I] [Fintype J] {d n r j:ℕ}
abbrev PAD (I:Type) := I→ℝ
abbrev Mat (I:Type) :=Matrix I I ℝ
def Semester (A:Mat I)(p:Pole (PAD I) (r+2)): Pole (PAD I) r:= ∑ i:I,∑ j:I,A i j • (p.curryLeft (Pi.single i 1)).curryLeft (Pi.single j 1)
lemma stanzaR (A:Mat I)(p:Pole (PAD I) (r+2))(x: Fin r→PAD I) : Semester A p x = ∑ i:I,∑ j:I,A i j * p (Fin.cons (Pi.single i 1) (Fin.cons (Pi.single j 1) x)):=by simp [Semester,ContinuousMultilinearMap.curryLeft_apply]
lemma semesterPlus (A:Mat I)(p q:Pole (PAD I) (r+2)): Semester A (p+q)=Semester A p+Semester A q := by ext1 x; simp only [stanzaR,_root_.add_apply,mul_add,Finset.sum_add_distrib]
lemma semesterScale (A:Mat I)(p:Pole (PAD I) (r+2))(c:ℝ): Semester A (c•p)=c • Semester A p:=by ext1 i; simp only [stanzaR,_root_.smul_apply,smul_eq_mul,Finset.mul_sum]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; ring
abbrev wind (r:ℕ):ℝ:= (r+2:ℕ)*(r+1:ℕ)
def opus (A:Mat I):End ℝ (Song (PAD I)) where
    toFun p r:= wind r • Semester A (p (r+2))
    map_add' p q:= funext fun r=> by rw [Pi.add_apply]; rw [semesterPlus,smul_add]; rfl
    map_smul' x p:=funext fun r=>by change wind _ • Semester A (x • p _) =x • _;rw [semesterScale,smul_comm]
variable {q:Song (PAD I)}
lemma semZ (A:Mat I) (r:ℕ): Semester A (r:=r) 0=0:=by ext1 i; simp only [stanzaR, _root_.zero_apply,mul_zero,sum_const_zero] -- deprecated
lemma opusReducer (A:Mat I) (c:ℝ): reduces (harmon (PAD I)) (c • opus A) := by
     rintro i p ⟨h,hp⟩; have he (q:ℕ)(hx:q+2>i): (c • opus A) p q=0:=by rw [LinearMap.smul_apply,Pi.smul_apply]; change c • (wind q • Semester A (p (q+2)))=_;rw [h (q+2) hx,semZ,smul_zero,smul_zero]
     refine ⟨fun hk=> funext fun q=>he q (by omega),⟨fun q hq=> he q (by omega),fun q u v=>?_⟩⟩; change (c • (wind q • Semester A (p (q+2)))) _ = (c • (wind q • _ : Pole (PAD I) q)) u; simp only [_root_.smul_apply]; have hz (j k:PAD I):= Libra.Coin.hark2 _ k (Libra.Coin.hark2 _ j (hp (q+2))); unfold Semester; simp only [_root_.sum_apply,_root_.smul_apply,hz _ _ u v]
lemma flavorDist (A B:Mat I): opus (A+B)=opus A+opus B:= by
     ext p r u
     change (wind r • Semester (A+B) (p (r+2))) u=(wind r • Semester A (p (r+2))+wind r • Semester B (p (r+2))) u; simp_rw [_root_.add_apply,_root_.smul_apply,stanzaR,Matrix.add_apply,add_mul,Finset.sum_add_distrib]; ring
-- contraction pad commutes for sym. Fin swap
lemma flipC (p:Pole E (r+2))(h:Tensor.Sym p)(a b:E): (p.curryLeft a).curryLeft b=(p.curryLeft b).curryLeft a:=by
     ext1 u; change p (Fin.cons a (Fin.cons b u))= _; let g:=Equiv.swap (0:Fin (r+2)) 1; rw [show Fin.cons a (Fin.cons b u)=Fin.cons b (Fin.cons a u) ∘ g from ?_]; exact h ..
     funext t; refine Fin.cases ?_ (fun i=>Fin.cases ?_ (fun j=>?_) i) t
     · simp [g]
     · simp [g]
     simp only [g,Function.comp_apply]; rw [Equiv.swap_apply_of_ne_of_ne (by simp) (by exact Fin.succ_inj.not.mpr (Fin.succ_ne_zero _))]; simp
lemma limits (p:Pole (PAD I) (r+4))(hp:Tensor.Sym p)(A B:Mat I): Semester A (Semester B p)=Semester B (Semester A p):=by
     have hv(a b c d:PAD I): (((p.curryLeft a).curryLeft b).curryLeft c).curryLeft d=(((p.curryLeft c).curryLeft d).curryLeft a).curryLeft b:=by
          have hh(x:PAD I):= Libra.Coin.hark2 p x hp
          rw [flipC _ (hh _) b c,flipC _ hp a c,flipC _ (Libra.Coin.hark2 _ a (hh _)) b d,flipC _ (hh _) a d]
     ext1 u; simp_rw [stanzaR,Finset.mul_sum]; let V (i:I): PAD I:=Pi.single i 1; let f(a b:I×I):= A a.1 a.2 * (B b.1 b.2 * p (Fin.cons (V b.1) (Fin.cons (V b.2) (Fin.cons (V a.1) (Fin.cons (V a.2) u)))))
     rw [show (∑ i:I, ∑ j:I,∑ k:I,∑ l:I, f (i,j) (k,l))=∑ a:I×I,∑ b:I×I,f a b from ?_, Finset.sum_comm]; swap; · simp_rw [Fintype.sum_prod_type]
     simp_rw [Fintype.sum_prod_type]; unfold f; refine sum_congr rfl (fun i _=>sum_congr rfl fun j _=>sum_congr rfl fun k _=>sum_congr rfl fun l _=>?_); rw [mul_left_comm]; exact congr_arg (fun z => B i j * (A k l * z)) (DFunLike.congr_fun (hv (V i) (V j) (V k) (V l)) u)

lemma commuteO (p:Song (PAD I))(h:p ∈ harmon (PAD I) r)(A B:Mat I)(c d:ℝ): (c • opus A) ((d • opus B) p) = (d • opus B) ((c • opus A) p):=by
     have hp:∀ i,Tensor.Sym (p i):=h.2; simp only [LinearMap.smul_apply,map_smul]; rw [smul_comm c d]; funext k; change (d • c • wind k • Semester A (wind _ • Semester B (p (k+4))))=(d • c • wind k • Semester B (wind _ • Semester A (p (k+4)))); rw [semesterScale,semesterScale,limits _ (hp _) _ _]
lemma rim_exp (p:Song (PAD I))(h:p ∈ harmon (PAD I) r)(A B:Mat I)(s t x:ℝ) (hp:r ≤ d): fixExp (s • opus A) x d (fixExp (t • opus B) x d p)=fixExp (s • opus A+t • opus B) x d p:=equations (opusReducer _ _) (opusReducer _ _) (fun _ p h=> commuteO p h A B s t) p h x d hp
end YM.OPE.Silt
