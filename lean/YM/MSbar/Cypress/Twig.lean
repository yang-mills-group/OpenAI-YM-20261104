import YM.MSbar.Spruce.Chop
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Cypress
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Lapaz
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal
variable {σ:Type} [Fintype σ]
variable (x:Positions σ)(f':Positions σ→ℝ)(L:List σ)(i:σ)
noncomputable def logK (f:Positions σ→ℝ) := fun i=>Real.log (f i)
lemma twig (he:∀ t, ContDiff ℝ (↑(t:ℕ)) f')(hp:∀ x,0<f' x) : buoy f' x (L++[i])/f' x= Yarn L.length (fun h:List Bool=>buoy f' x (takeout true h L)/ f' x *buoy (logK f') x (takeout false h L ++ [i])):=by
    let f:= f'; let g:= logK f'; let n:=L.length; let h:=Duel.stallA g i; have hv:ContDiff ℝ (↑(n+1:ℕ)) g:=(he (n+1)).log fun i=> (hp i).ne'; have hh:ContDiff ℝ (↑(n+1:ℕ)) f:=he _; have he: Duel.stallA f i=(f*h):=by
           let H(y:Positions σ):=Real.exp (g y); have ht(x):H x=f x:=Real.exp_log (hp x)
           nth_rw 1 [←funext ht]; funext z; unfold H Duel.stallA; rw [(hv.differentiable (by simp) z).hasFDerivAt.exp.fderiv]; change H z*h z=f z*h z; rw [ht] -- pattern
    have hx(l:List σ)(hx:l.length≤ n)(f:Positions σ→ℝ)(h:ContDiff ℝ (↑(n+1:ℕ)) f): buoy f x (l++[i])= buoy (Duel.stallA f i) x l:= by unfold buoy; simp only [List.map_append,List.map_cons,List.map_nil]; rw [Lis.fore (n+1) h.contDiffAt, Lis.takeG (n+1) h.contDiffAt]; rfl; all_goals rw [List.length_map]; omega
    have ht:ContDiffAt ℝ n f x:= hh.contDiffAt.of_le (by exact_mod_cast Nat.le_succ n); rw [hx L le_rfl f hh,he,paisley n f h _ _ ht ((hv.contDiffAt.fderiv_right (m:= (n:ℕ∞ω)) (by simp)).clm_apply (g:=fun _=> (@bolt σ i)) contDiffAt_const) le_rfl, div_eq_mul_inv,← poker]; refine stitch _ fun v ht=> ?_; rw [show buoy h _ _= _ from (hx (takeout false v L) ((sunset _ v L ht).trans_le ((part_le ..).trans_eq ht)) g hv).symm]; unfold f g; ring
lemma alone (f:List Bool→ℝ)(p:ℕ) (g:ℝ): Yarn p (fun l:List Bool=> if true ∈ l then f l else g)= g+Yarn p (fun l:List Bool=> if true∈l then f l else 0):=by
    induction p generalizing f with
    | zero=>simp [Yarn]
    | succ i ih=> let k(L):=f (false::L); rw [twilled,twilled]; simp_rw [Fintype.sum_bool]; have hu :=ih k
                  simp only [List.mem_cons,true_or,if_true,Bool.true_eq_false,false_or] at *; rw [← show g+Yarn _ _=_ from hu.symm]; unfold k; abel
lemma takeout_ghost {T:List Bool}(h : T.length=L.length)(hp:true∉T): takeout false T L=L ∧ takeout true T L=[]:=by induction L generalizing T with
    | nil=> have hv:T=[]:=List.eq_nil_of_length_eq_zero h; rw [hv]; exact ⟨rfl,rfl⟩
    | cons i l ih=> cases T with
                    | nil=> simp at h
                    | cons a T=>
                          cases a; swap; · simp at hp
                          simp only [List.length_cons,Nat.succ_inj] at h; obtain ⟨ha,hb⟩:= ih h (fun hh=> hp (List.mem_cons_of_mem _ hh)); change i::takeout false T l=i::l ∧ takeout true T l=[]; rw [ha,hb]; simp
lemma streak (T:List Bool)(h:T.length=L.length)(hp:true∈T): (takeout false T L).length < L.length:=by
     rw [sunset _ _ _ h,← h]; clear h; induction T with
     | nil=> simp at hp
     | cons a T ih=> cases a
                     · simp only [List.mem_cons,Bool.true_eq_false,false_or] at hp; exact Nat.succ_lt_succ (ih hp) -- dependency
                     have hx: parts false T≤ T.length:=part_le ..; change parts false T<T.length+1; omega
end YM.MSbar.Cypress
