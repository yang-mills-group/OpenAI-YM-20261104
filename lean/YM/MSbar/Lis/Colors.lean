import YM.MSbar.Lis.Glove
import YM.MSbar.Lis.Province
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Lis
open Function Filter Whisk Push Uniform Lattice RG
open Precision Measuring
open scoped Topology BigOperators Classical ContDiff
variable {σ ι M N:Type} [Fintype σ][Fintype ι][NormedAddCommGroup M][NormedSpace ℝ M]
local notation "X"=>Positions σ
variable (p:ℕ)(i:σ)(l:List M){x:M}
lemma ores (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](v:E→L[ℝ]ℝ)(f:M→E)(he:ContDiffAt ℝ p f x)(h:l.length≤p) : roc (v ∘ f) l x= v (roc f l x):=by
    induction l generalizing x with
    | nil=>rfl
    | cons a l ih=>
       have hh : roc (v ∘ f) l =ᶠ[𝓝 x] v ∘ roc f l:= (he.eventually (by simp)).mono (fun i hf=>ih hf (by simp only [List.length_cons] at h;omega)); have hf:DifferentiableAt ℝ (roc f l) x:= (smooth p 1 l he (by simp only [List.length_cons] at h;omega)).differentiableAt (by simp)
       rw [roc,roc,hh.fderiv_eq, fderiv_comp _ v.differentiableAt hf, v.fderiv];rfl
lemma addedL (f g:M→ℝ)(hf: ContDiffAt ℝ p f x)(hg:ContDiffAt ℝ p g x)(h:l.length≤p):roc (f+g) l x= roc f l x+roc g l x:=by
    induction l generalizing x with |nil=> rfl|cons a l ih=>
      have hh:1+l.length≤p:=by rw [List.length_cons] at h;omega
      have he: roc (f+g) l=ᶠ[𝓝 x] roc f l + roc g l:= ((hf.eventually (by simp)).and (hg.eventually (by simp))).mono (fun i hv=> ih hv.1 hv.2 (by omega))
      rw [roc,roc,roc,he.fderiv_eq,fderiv_add ((smooth p 1 l hf hh).differentiableAt (by simp)) ((smooth p 1 l hg hh).differentiableAt (by simp))];rfl
lemma wed (a:ℝ)(f : M→ℝ)(hf:ContDiffAt ℝ p f x)(he:l.length≤p): roc (fun x=> a*f x) l x= a*roc f l x:= by exact ores p l ℝ (a • ContinuousLinearMap.id ℝ ℝ) f hf he
lemma tot (s:Finset ι)(f:ι→M→ℝ)(h:∀ i∈s,ContDiffAt ℝ p (f i) x)(he:l.length≤p) : roc (fun i=>∑ j∈s,f j i) l x=∑ j∈s,roc (f j) l x:=by
    induction s using Finset.induction with
    | empty=> simpa using (show roc (fun _ :M=> (0:ℝ)) l x=0 from (by cases l with |nil=> rfl |cons a l=> -- roc zero global by induction
                                                                           have hh(l:List M): roc (fun _ :M=> (0:ℝ)) l=0:=by induction l with|nil=>rfl|cons a l ih=>funext y; simp [roc,ih]
                                                                           exact congrFun (hh _) x))
    | insert a s hp IH=> simp_rw [Finset.sum_insert hp]; have hh : ∀ i∈s,ContDiffAt ℝ p (f i) x:=fun i hi=>h _ (Finset.mem_insert_of_mem hi); rw [← IH hh]; apply addedL p l (f a) (fun i=>∑ j∈s,f j i) (h a (Finset.mem_insert_self ..)) (ContDiffAt.sum hh) he
-- list split Leib.Z.fore.Early
lemma taken_len (b:Bool)(s:List Bool)(h:s.length=l.length) : (takeout b s l).length≤l.length:= by induction l generalizing s with|nil=> rw [show s=[] by simpa using h]; rfl|cons a l ih=> cases s with|nil=>simp at h | cons i s=> have ht:= ih s (by simpa using h); rw [takeout]; split <;> simp only [List.length_cons] <;> omega
lemma der_y (c : M) (f:List σ→ M→ℝ)(x:M)(h :∀ l:List σ,l.length=p→DifferentiableAt ℝ (f l) x) : fderiv ℝ (fun y=> Yarn p (fun i=> f i y)) x c= Yarn p (fun i=> fderiv ℝ (f i) x c):=by
    have ht(p:ℕ)(f:List σ→M→ℝ)(h:∀ l,l.length=p→DifferentiableAt ℝ (f l) x): ∃ v:M→L[ℝ]ℝ, HasFDerivAt (fun y=> Yarn p (fun i=> f i y)) v x ∧ v c= Yarn p (fun i=> fderiv ℝ (f i) x c):=by
       induction p generalizing f with
       | zero=> exact ⟨_,(h [] rfl).hasFDerivAt,rfl⟩
       | succ p ih=>
          choose v hv hc using fun a:σ=>ih (fun i=>f (a::i)) (fun l hl=> h (a::l) (by simp [hl]))
          simp_rw [twilled]; refine ⟨_,HasFDerivAt.fun_sum (fun i _=> hv i),?_⟩; rw [_root_.sum_apply]; simp [hc] -- uncertain
    obtain ⟨v,h1,h2⟩:= ht p f h; rw [h1.fderiv,h2]
lemma poly (f g:M→ℝ)(hx:ContDiffAt ℝ p f x)(hg:ContDiffAt ℝ p g x)(h:l.length≤p):roc (f*g) l x=Yarn l.length fun T:List Bool=> roc f (takeout true T l) x*roc g (takeout false T l) x:=by
    induction l generalizing x with
    | nil=>rfl
    | cons a t ih=>
       let v(i:List Bool)(x:M):= roc f (takeout true i t) x*roc g (takeout false i t) x; have hp :1+t.length ≤p:=by rw [List.length_cons] at h; omega
       have hv : roc (f*g) t=ᶠ[𝓝 x] (fun y=> Yarn t.length fun i=>v i y):= ((hx.eventually (by simp)).and (hg.eventually (by simp))).mono (fun i h=> ih h.1 h.2 (by omega)); have hW (f:M→ℝ)(hf:ContDiffAt ℝ p f x)(b:Bool)(s:List Bool)(hx:s.length=t.length):DifferentiableAt ℝ (roc f (takeout b s t)) x:= (smooth p 1 _ hf ((Nat.add_le_add_left (taken_len t b s hx) _).trans hp)).differentiableAt (by simp)
       rw [roc,hv.fderiv_eq, der_y t.length a v x (fun l hl=> (hW f hx _ l hl).mul (hW g hg _ l hl)), List.length_cons, twilled,Fintype.sum_bool, ← pockets]; refine stitch t.length fun i hi=>?_ ; unfold v;rw [fderiv_fun_mul (hW f hx true i hi) (hW g hg false i hi)]; simp only [takeout, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false,_root_.add_apply, _root_.smul_apply,roc]; change _=_; push_cast; ring -- need elim false
lemma paisley(f g:X→ℝ)(x:X)(l:List σ)(hf:ContDiffAt ℝ p f x)(hh:ContDiffAt ℝ p g x)(he:l.length≤p) : buoy (f*g) x l= Yarn l.length fun T:List Bool=> buoy f x (takeout true T l)*buoy g x (takeout false T l) :=by
    unfold buoy; rw [poly p _ f g hf hh (by simpa only [List.length_map]),List.length_map]; refine stitch l.length fun k hk=>?_ ; have hx (t:List Bool)(l:List σ)(b:Bool):takeout b t (l.map Uniform.bolt)=(takeout b t l).map Uniform.bolt:=by
        induction l generalizing t with|nil=> cases t <;> rfl|cons a l ih=> cases t with |nil=>rfl|cons c t=> by_cases he:c=b <;> simp [takeout,he,ih]
    rw [hx,hx]
lemma emptyF {f:M →ℝ}(x:M) (L:List M)(h:0∈ L)(hf:ContDiffAt ℝ p f x)(he:L.length ≤ p): roc f L x=0:=by
    obtain ⟨l,t,ht⟩:= List.append_of_mem h; subst L
    rw [echo p hf _ (0::(l++t)) he List.perm_middle,roc,map_zero]
end YM.MSbar.Lis
