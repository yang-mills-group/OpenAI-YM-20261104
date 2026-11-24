import YM.OPE.Compatible.Stamen.Cleft
/-!
# Wick drag on infinite support gauge frames, fixed period as chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Phere
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08 Float
open scoped Topology BigOperators Classical
variable {I G K E F X:Type}{m r i j n k:ℕ}{C D:ℝ} {H:Gauge}
open Cloud JetS
open scoped ContDiff
variable {v y:fieldX (Shade H)}
open Tensor WardBin
-- budget C estimate.O. Use masks of bad axes
section Crest
variable (p:Script (Shade H) k)(hp: soot m p C)(hk: k+4 ≤ m)(hv: Quiet v 0)
local notation "X"=> fieldX (Shade H)
-- generalized quiet.S template.Pass.
def lent (a:Finset (Fin k))(v w:X)(i:Fin k): X:= if i∈a then w else v
include hk in
lemma QuietMot (n:ℕ)(w y:X)(h:Quiet w 1)(ht:Quiet y n)(a:Finset (Fin k))(hp:a.card*n ≤ 4): Glob (lent a w y) (fun i=> 1+(if i∈a then n else 0)) ∧ (∑ i:Fin k, (1 + if i∈a then n else 0))≤m:=by
       constructor
       · intro i; unfold lent; dsimp only; by_cases hx:i∈a; rw [if_pos hx,if_pos hx]; exact quiet_up ht (by omega); rw [if_neg hx,if_neg hx]; exact h
       rw [Finset.sum_add_distrib]; rw [← Finset.sum_filter]; simp; omega
include hp hk hv
lemma canopy (n:ℕ)(w:X)(hw:Quiet w n)(a:Finset (Fin k))(h:a.card*n≤4): Summable fun i=>p i*wordX (lent a (alpha v) w) i:= wordSum hp (QuietMot hk n (alpha v) w (plumQ v hv 1) hw a h).1 (QuietMot hk n (alpha v) w (plumQ v hv 1) hw a h).2
lemma charcoal (n:ℕ)(w:X)(hw:Quiet w n)(a:Finset (Fin k))(h:a.card*n≤4)(hh:p.abides): wholeX p (lent a (alpha v) w)=wholeX p (lent a v w):=by
       let K(i:Fin k):ℕ:= 1+(if i∈a then n else 0); let q:= alpha v
       obtain ⟨h1,h2⟩:= QuietMot hk n (alpha v) w (plumQ v hv 1) hw a h; have hx: Glob (lent a v w) K:=(QuietMot hk n v w (quiet_up hv (by omega)) hw a h).1
       let V(sa: Finset (Fin k))(i:Fin k):= if i∈ sa then lent a q w i else lent a v w i; have he(sa:Finset (Fin k)): Glob (V sa) K:=fun i=>by unfold V;split;exact h1 _; exact hx _
       have ht(sa:Finset (Fin k)): wholeX p (V sa)= _:= (show wholeX p (V sa)=wholeX p (lent a v w) from (by
           induction sa using Finset.induction_on with
           | empty=>simp [V]
           | insert i sa hj ih=>
                  by_cases hy:i∈a
                  · rw [show V (insert i sa)=V sa from (by funext j; by_cases hu:j=i<;> simp [V,lent,hy,hu])];exact ih
                  let c:= candor v; let T:= update (V sa) i (mountain c); have hc:Quiet c (K i):= quiet_up (normPost' _ hv) (by unfold K; omega); have hv:Glob T K:=by intro x; by_cases hm:x=i; subst x; rw[show T i= _ from update_self ..]; exact heather hc; rw [show T x= _ from update_of_ne hm ..]; exact he sa x
                  have hb: V (insert i sa) i= V sa i+ T i:=by unfold V T; rw[if_pos (mem_insert_self ..), if_neg hj, update_self]; change (if _ then _ else q)= (if _ then _ else v)+_; rw [if_neg hy,if_neg hy];exact funext fun _=>moreH ..
                  rw [choir i hp (he sa) hv h2 hb (fun j hj=>by simp [V,T,hj]),ih,show wholeX p T=0 from crest_zero p hh hp _ i c K h2 (fun j _=>he sa j) hc, add_zero]))
       simpa only [V,Finset.mem_univ,if_true] using ht univ
end Crest
end YM.OPE.Silt.Phere
