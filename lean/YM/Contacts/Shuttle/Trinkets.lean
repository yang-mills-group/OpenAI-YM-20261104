import YM.Contacts.Shuttle.Folds
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Shuttle.Trace.Quill
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix
open MeasureTheory Analysis Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Pulse Pulse.Spine Origin
open Milling Milling.Steam Milling.Forge Tensor MultiNext.SignedSource Pattern Tide Morning
open scoped Classical Topology BigOperators NNReal ENNReal Matrix ContDiff
variable {G:Gauge}{b h d k r n u:ℕ}{X Y:Type}{F: Cohort G}
def play (b:Hood k X) : Tailor k ↪ Hood k (Node X):= ⟨fun x i=>(lap x i,b i), fun a z he=> funext fun ⟨i,j⟩ => congr_fun (congr_arg Prod.fst (congr_fun he i)) j⟩
lemma catches (x:Hood k (Node X))(b:Hood k X): Prod.snd∘ x=b→ x∈ Set.range (play b):= fun h=> ⟨fun a=>(x a.1).1 a.2, funext fun i=> Prod.ext rfl (congr_fun h i).symm⟩ -- Prod.snd x = b orientation
abbrev citron (z:X)(g:E4→ℝ)(x:Node X) := if x.2=z then g (xyz x.1) else 0
lemma captain (b:Dyes G)(f:E4→ℝ)(hf:f∈ Powers.space E4 ℝ k) : ∃ g:Axis→E4→G.Color,(∀ a,g a∈ Powers.space E4 G.Color k) ∧ ∀ z a (l:G.ColorIndex),citron b f (z,coord a,l)=g a (xyz z) l:= by
   let u:G.Color:=EuclideanSpace.single b.2 1; let L : ℝ→L[ℝ] G.Color:=(ContinuousLinearMap.id ℝ ℝ).smulRight u; refine ⟨fun a x=> if coord a=b.1 then L (f x) else 0,fun a=>?_,fun z a l=>?_ ⟩
   · by_cases he: coord a=b.1 <;> simp only [he, ↓reduceIte]; exact Powers.carried L hf; exact Powers.constants 0 _
   by_cases he:coord a=b.1; · simp_rw [he,if_true]; unfold citron L u; obtain ⟨p,w⟩:=b; simp [Prod.ext_iff]
   dsimp only; rw [if_neg he]; unfold citron; rw [if_neg (show (coord a,l)≠b from fun h=> he (congr_arg Prod.fst h))]; rfl
-- `ash` costs include convergence certificate
abbrev fell (f:Field (Fin k) (Node X)) (b:Hood k X)(p: Tailor k→ℝ) (x:Tailor k):= f (play b x) * p x
def silenced (f:Field (Fin k) (Node X))(r:ℕ): Prop := ∀ b:Hood k X,∀ j<r,∀ p∈ Throng j k, HasSum (fell f b p) 0
lemma silence (A:Tide.Tags F)(ha:h≤d)(hb:d≤n)(hc:d*(d+1)≤u)(hy:unreads F d u n h) (ht:k ≤h) : silenced (F k) (h-k+1):= by
   intro b j hj p he; refine Submodule.span_induction (p:=fun p _=> HasSum (fell (F k) b p) 0) ?_ ?_ ?_ ?_ he
   · rintro t ⟨p,d,hp,hd,rfl⟩; let f (i: Fin k):=citron (b i) (p i); choose a hA h' using fun i=> lung (Powers.widen (d i) j ((single_le_sum (f:=d) (s:=univ) (fun i _=> Nat.zero_le _) (mem_univ i)).trans hd) (hp i)); obtain ⟨x,s,hs,y,hY⟩:= (A.alone k); have hs:= hY.calls hs (Finset.sum_nonneg (s:=univ) fun i _=> hA i) (v:=f) (n:=j)  (by
        intro i v
        unfold f citron; split
        next hx=> apply (h' i v.1 v.1 le_rfl).trans; exact mul_le_mul_of_nonneg_right (single_le_sum (fun i _=> hA i) (mem_univ _)) (by change 0≤ (1+(size v.1:ℝ))^j; positivity)
        next hh=> rw [norm_zero]; exact mul_nonneg (sum_nonneg (fun i _=>hA _)) (by unfold blast; positivity))
     let t(x:Tailor k):= books x p; let c := F k; let w:=fun x=> (c x)*(∏ i,f i (x i)); have hw: w ∘ (play b)=fell c b t:= by funext x; unfold w fell t; simp [play,books,f,citron,Function.comp_apply]
     rw [show _=fell c b t from rfl, ← hw]; let q:= F k; have hh:say (F k) f=0:= Tide.Morning.moment_null A ha hb hc hy (fun i=> d i+1) f (fun i=> captain (b i) (p i) (hp i)) (by simp) (by rw [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,smul_eq_mul,mul_one]; omega); refine ((play b).injective.hasSum_iff ?_).2 (hh ▸ hs.hasSum) -- orientation!
     intro i hi; have he : ∃ u, (i u).2≠b u:= by by_contra! e; exact hi (catches i b (funext e))
     obtain ⟨u,hu⟩:= he; unfold w; rw [prod_eq_zero (mem_univ u),mul_zero]; exact if_neg hu
   · change HasSum (fell (F k) b 0) 0; unfold fell; simpa only [fell, Pi.zero_apply, mul_zero] using (hasSum_zero (α:=ℝ) (β:=Tailor k)) -- names
   · intro x y _ _ hx hy; unfold fell; simpa only [fell,Pi.add_apply,mul_add,add_zero] using hx.add hy
   intro a x _ hx; unfold fell; simpa only [fell, Pi.smul_apply, smul_eq_mul,mul_left_comm (F k _),mul_zero] using (hx.mul_left a) -- simp expr F k_
end YM.Contacts.Shuttle.Trace.Quill
