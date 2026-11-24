import YM.MSbar.Lis.Glove
import YM.MSbar.MeasureP.Shuttle
import YM.Push.STATIONARY_UNIFORM.Array
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Lis
open Function Filter Whisk Push Uniform Lattice RG
open scoped Topology BigOperators ContDiff Classical
variable {σ ι M N K: Type} [Fintype σ] [Fintype ι] {c n:Side}
noncomputable def buoy (f: Positions σ→ℝ)(x:Positions σ)(l:List σ) : ℝ:= roc f (l.map Uniform.bolt) x -- coe implicit bolt. 
variable (m:ℕ) (u:σ→Site n) (v:ι→Site c) (a w:ℝ) (p:ℕ)
lemma spiral(v:Positions σ): v=∑ x:σ, v x • bolt x:=by
    funext i; rw [Finset.sum_apply]; simp only [bolt,Pi.smul_apply,smul_eq_mul,Pi.single_apply]; simp -- tag
open Measuring
lemma paint (f:Positions σ→ℝ)(u:Positions ι→L[ℝ] Positions σ)(l:List ι)(x:Positions ι) (k:ℕ)(h:ContDiffAt ℝ k f (u x))(hk:l.length≤k) : buoy (f∘ u) x l=shaft l.length (fun j i=> u (bolt i) j) (buoy f (u x)) l:=by
   let g(j)(i) := u (bolt i) j; let m':=u x
   unfold buoy; rw [toe u k (l.map bolt) h (by simpa only [List.length_map] using hk)]
   have he(l:List ι)(t:List σ)(hp:l.length+t.length≤k) : roc f ((t.map bolt)++ (l.map bolt).map u) m'=Yarn l.length (fun j=> roc f ((t++j).map bolt) m' * beads g j l):=by
       induction l generalizing t with
       | nil=> simp [Yarn,beads]
       | cons i z ih=>
          let v(i:ι):=u (bolt i); let r:=(List.map u (z.map bolt)); have hx:t.length+z.length< k:=by rw [List.length_cons] at hp;omega
          let w(t':List (Positions σ)):= roc f t' m'
          have hs : w (t.map bolt ++(u (bolt i)::r))=∑ j:σ,g j i*w (((t++[j]).map bolt)++ r):=by
              unfold w; nth_rw 1 [spiral (u (bolt i))]; rw [num ..]; refine Finset.sum_congr rfl fun j _=>?_ ; simp [g]; exact k; exact h; unfold r; simpa only [List.length_map] using hx -- app
          rw [List.length_cons,twilled,List.map_cons,List.map_cons]; unfold w at hs; rw [show roc _ _ _=_ from hs]; refine Finset.sum_congr rfl fun j _=>?_ 
          rw [show roc f _ _= _ from ih (t++[j]) (by simp only [List.length_append,List.length_cons,List.length_nil]; omega),←sheen]; apply stitch; intro T _; simp only [List.append_assoc,List.cons_append,List.nil_append,beads]; ring
   exact (he l [] (by simp [hk])).trans (by change Yarn _ _=Yarn _ _; apply stitch; intro i _; rfl)
-- Tapes norms. W zero field derivatives at 1..p and cash center extension all centers smooth. single radius.
open Metric Set
variable (t:σ→Site n) (F:Positions σ→ℝ)
structure JetTab (t:σ→Site n)(a:ℝ)(p:ℕ)(w:ℝ)(S:Set (Positions σ))(f:Positions σ→ℝ)(m:ℕ)(B:ℝ) : Prop where
   zeroP : 0 ≤ B
   sold : ∃ g:List σ→ℝ, (∀ l:List σ,l.length=m+1→ 0≤g l ∧ ∀ x∈S,|buoy f x l| *w^(m+1)≤g l)∧∀ i:σ,Yarn m (fun l=> g (i::l)*swipe t a p (i::l)) ≤ B
namespace JetTab
variable {S S':Set (Positions σ)} {t:σ→Site n}{a w B B' :ℝ}{p m:ℕ}{F:Positions σ→ℝ}
lemma cast (h:JetTab t a p w S F m B)(he:B ≤ B')(hh:S'⊆S):JetTab t a p w S' F m B':=by
    obtain ⟨hp,g,hf,hg⟩:= h; exact ⟨hp.trans he,g,fun l hi=>⟨(hf l hi).1,fun x hx=>hf l hi|>.2 x (hh hx)⟩,fun i=>(hg i).trans he⟩
local notation "π"=> (fun l=>swipe t a p l)
lemma count (h:JetTab t a p w S F m B)(hw:0<w)(x:Positions σ)(hx:x∈S)(b:σ):Yarn m (fun l:List σ=>|buoy F x (b::l)| *swipe t a p (b::l))≤B/w^(m+1):=by
   obtain ⟨_,g,hf,hg⟩:=h; rw [le_div_iff₀ (pow_pos hw _)]; let f j:= buoy F x (b::j); have hy(i:List σ):0≤swipe t a p i:= effect ..|>.le
   rw [mul_comm,← sheen]; apply le_trans _ (hg b); refine shiny m fun j hi=>?_ ; have ht:(b::j).length=m+1:=by rw [List.length_cons,hi]
   exact le_trans (le_of_eq (by ring)) (mul_le_mul_of_nonneg_right (hf _ ht|>.2 x hx) (hy _))
lemma grant (h:∀ i:σ,Yarn m (fun l=>|buoy F 0 (i::l)| *swipe t a p (i::l)) ≤ B/w^(m+1)) (he:0≤B)(hw:0<w): JetTab t a p w {0} F m B :=by
   refine ⟨he,fun l=>|buoy F 0 l| *w^(m+1),fun l hx=>⟨by positivity,fun i hi=>?_⟩,fun i=>?_⟩
   · rw [Set.mem_singleton_iff.mp hi]
   have hh:= le_div_iff₀ (pow_pos hw _)|>.mp (h i); refine le_trans ?_ hh; rw [mul_comm (Yarn _ _),←sheen]; apply shiny; intro T h; exact le_of_eq (by ring)
end JetTab
end YM.MSbar.Lis
