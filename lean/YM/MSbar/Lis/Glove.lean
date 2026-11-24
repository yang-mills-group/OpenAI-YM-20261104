import YM.MSbar.MeasureP.Dusk
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Lis
open Function Filter Whisk
open scoped Topology BigOperators Classical ContDiff
variable {σ ι M N K: Type} [NormedAddCommGroup M][NormedSpace ℝ M][NormedAddCommGroup N][NormedSpace ℝ N][NormedAddCommGroup K][NormedSpace ℝ K]
noncomputable def roc (f:M→N): List M → M→N
| [],x=> f x
| i::l,x=>fderiv ℝ (roc f l) x i
lemma smooth (p q:ℕ) (u: List M){f:M→N} {x:M}(h:ContDiffAt ℝ p f x)(hx:q+u.length ≤ p): ContDiffAt ℝ q (roc f u) x:=by
    induction u generalizing q with
    | nil=> change ContDiffAt ℝ q f x; exact h.of_le (by exact_mod_cast (show q≤ p from by simpa using hx))
    | cons a l ih=> exact ((ih (q+1) (by rw [List.length_cons] at hx; omega)).fderiv_right (by simp)).clm_apply contDiffAt_const -- map q?
lemma follows {f g:M→N} (l:List M){x:M}(h:f=ᶠ[𝓝 x] g): roc f l=ᶠ[𝓝 x] roc g l:= by induction l with |nil=>exact h|cons a l ih=> filter_upwards [ih.fderiv (𝕜:=ℝ)] with x he; rw [roc,roc,he]
lemma reflect {f:M→N} (k:ℕ)(l m:List M)(a b:M){x:M} (hp:k≥ l.length+m.length+2) (hx:ContDiffAt ℝ k f x) : roc f (l++a::b::m) x= roc f (l++b::a::m) x :=by
    induction l generalizing x with
    | nil=>
       have hh : ContDiffAt ℝ (↑(2:ℕ)) (roc f m) x:= smooth k 2 m hx (by simp only [List.length_nil,zero_add] at hp; omega)
       let j:=fderiv ℝ (roc f m); have hv: DifferentiableAt ℝ j x :=(hh.fderiv_right (show (1:WithTop ℕ∞)+1≤ (2:ℕ) by norm_num)).differentiableAt (by simp)
       have ht(i i'):roc f (i::i'::m) x= fderiv ℝ j x i i':=by
            let A:=ContinuousLinearMap.apply ℝ N i'; change fderiv ℝ (A ∘ j) x i= _; rw [fderiv_comp _ A.differentiableAt hv,A.fderiv]; rfl
       rw [List.nil_append,List.nil_append,ht,ht]; exact hh.isSymmSndFDerivAt (by norm_num) a b
    | cons v l ih=>
       have hp' : (l.length+m.length+2) ≤ k:=by rw [List.length_cons] at hp;omega
       rw [List.cons_append,List.cons_append,roc,roc]; congr 1 -- may overcongr
       exact (show roc f (l++a::b::m) =ᶠ[𝓝 x] roc f (l++b::a::m) from (hx.eventually (by simp)).mono (fun x hy=> ih hp' hy)).fderiv_eq (𝕜:=ℝ)
lemma echo {f:M→N}(k:ℕ){x:M}(h:ContDiffAt ℝ k f x)(l m:List M)(he:l.length≤k)(hp:l.Perm m) : roc f l x=roc f m x :=by
    -- swap at extension
    have ht(l m:List M)(hp:l.Perm m):∀ i:List M,i.length + l.length ≤k→ roc f (i++l) x=roc f (i++m) x:=by
       induction hp with
       | nil=>exact fun _ _=>rfl
       | cons a e ih=> intro i hi; have hh:= ih (i++[a]) (by simp only [List.length_append,List.length_cons,List.length_nil] at *; omega); simpa using hh
       | swap i j m=>intro l hl; exact Lis.reflect k l m _ _ (by simp only [List.length_cons] at *; omega) h
       | trans ha hb ih hh=>intro i he; rw [ih i he]; exact hh i (by rwa [← ha.length_eq])
    exact ht l m hp [] (by simp [he])
lemma fore {f:M→N}(k:ℕ){x:M}(h:ContDiffAt ℝ k f x)(l:List M)(i:M)(he:l.length<k): roc f (l++[i]) x=roc f (i::l) x:= echo k h (l++[i]) (i::l) (by simpa using he) (List.perm_append_comm ..) -- List arg order
lemma takeG {f:M→N}(k:ℕ){x:M}(h:ContDiffAt ℝ k f x)(L:List M)(i:M)(he:L.length<k) : roc f (i::L) x= roc (fun y=>fderiv ℝ f y i) L x:=by
    rw [←fore k h L i he]; clear h; induction L generalizing x with
    | nil=>rfl
    | cons j L ih=>rw [List.cons_append,roc,roc,show roc f (L++[i])=roc (fun y=>fderiv ℝ f y i) L from funext (fun y=>ih (x:=y) (by simp only [List.length_cons] at *; omega))]
lemma toe {f:M→N} (u : K→L[ℝ]M)(k:ℕ) (l:List K){x:K}(h:ContDiffAt ℝ k f (u x))(hh:l.length≤k) : roc (f∘ u) l x=roc f (l.map u) (u x):=by
    induction l generalizing x with
    | nil=>rfl
    | cons a l ih=>
       let g(y:N):= y
       have hv : DifferentiableAt ℝ (roc f (l.map u)) (u x):= (smooth k 1 (l.map u) h (by simp only [List.length_cons,List.length_map] at *; omega)).differentiableAt (by simp)
       have ht : roc (f ∘ u) l =ᶠ[𝓝 x] roc f (l.map u) ∘ u:= (u.continuous.continuousAt.eventually (h.eventually (by simp))).mono (fun i hi=> ih hi (by simp only [List.length_cons] at hh; omega))
       rw [roc,List.map_cons,roc,ht.fderiv_eq,fderiv_comp _ hv u.differentiableAt,u.fderiv]; rfl
-- plu derivative in single list
lemma mash {f:M→ℝ}(a: M)(l t:List M)(g:ι→M)(c:ι→ℝ)(s:Finset ι){x:M}(k:ℕ)(ha:ContDiffAt ℝ k f x)(hh:l.length+t.length < k) : roc f (l++((∑ i∈s,c i • g i)::t)) x=∑ i∈s,c i*roc f (l++(g i::t)) x:=by
    have he(i:M): roc f (l++(i::t)) x= fderiv ℝ (roc f (l++t)) x i:= echo k ha (l++(i::t)) (i::(l++t)) (by simp only [List.length_append,List.length_cons];omega) (List.perm_middle)
    simp_rw [he,map_sum,map_smul]; rfl
lemma num {f:M→ℝ}(l t:List M)(g:ι→M)(c:ι→ℝ)(s:Finset ι){x:M}(k:ℕ)(ha:ContDiffAt ℝ k f x)(hh:l.length+t.length < k) : roc f (l++((∑ i∈s,c i • g i)::t)) x=∑ i∈s,c i*roc f (l++(g i::t)) x:= mash (0:M) l t g c s _ ha hh
end YM.MSbar.Lis
