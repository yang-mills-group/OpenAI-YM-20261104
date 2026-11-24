import YM.RG06.Classical.Current

/-!
# Static YM equations through a finite demand, true nonlinear next extension

Use arbitrary g ∈ ℝ (not S.C universe trajectory!). Right inverse available every G from
constructed homogeneous ∂A analysis. Doesn't entail existence of convergent connection
solving globally with arbitrary jets, or vanishing of quantum Euler insertions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.ClassicalOn
open Function Analysis Continuum Tensor Vectorial Labels
open scoped ContDiff BigOperators Classical Matrix.Norms.Frobenius Topology
variable {G:Gauge}{i k d:ℕ}

def YMAt (g:ℝ)(d:ℕ)(J:Jet G):=∀ n,n+3≤d→ data g (radField d J) n=0
-- coherent all horizons. Need d physical horizon of gauge field, not covariance order.

def curt (j:ℕ)(u v:Jet G):Prop:= ∀ i<j,u i=v i
lemma cut {u v:Jet G}(h:curt (d-1) u v):radField d u=radField d v:=by funext i x; unfold radField Source.potential; exact Finset.sum_congr rfl (fun i hi=>by rw [h _ (Finset.mem_range.mp hi)])
lemma taxes {j:ℕ}(h:0<j)(u:Jet G):radField (j+1) u=radField j u+(u (j-1)).value:=by
 cases j with
 | zero=>contradiction
 | succ j=>
    funext i x; unfold radField Source.potential
    rw [show j+1+1-1=j+1 by omega,Finset.sum_range_succ]; rfl
lemma grading (j:ℕ)(u:Jet G) {v:Taylor G (j+1)}:radField (j+3) (update u (j+1) v)=radField (j+2) u+v.value:=by
 rw [taxes (j:=j+2) (by omega), show (j+2)-1=j+1 by omega,Function.update_self,cut (u:=update u (j+1) v) (v:=u) (fun i hi=>by rw [update_of_ne];omega)]

lemma behold (g:ℝ){k:ℕ}(u:Jet G)(i:ℕ)(hi:i ≤ k):
    data g (radField (k+3) u) i= data g (radField (k+2) u) i+ if i=k then offer k (u (k+1)) else 0:=by
 rw [taxes (j:=k+2) (by omega),show k+2-1=k+1 by omega,triangular g _ (rad_smooth _ _) (u _) i hi];
lemma reflects (g:ℝ)(u:Jet G)(h:i≤d):YMAt g d u→ YMAt g i u:=by
 suffices he : ∀ j:ℕ,YMAt g (j+1) u → YMAt g j u by
   induction d,h using Nat.le_induction with
   | base=>exact id
   | succ d H H'=> exact fun hD=>H' (he d hD)
 intro k h n hn
 cases k with
 | zero=>omega
 | succ k=>
    cases k with
    | zero=>omega
    | succ k=>
       have he:=h n (by omega)
       rw [show k+1+1+1=k+3 by omega, behold g u n (by omega),if_neg (by omega),add_zero] at he; exact he
lemma prior(g:ℝ)(u:Jet G)(k:ℕ)(h:YMAt g (k+2) u):Vectorial k (data g (radField (k+2) u) k):=
 allegiance g (radField _ _) (rad_smooth _ _) k (fun i hi=>h i (by omega))
lemma rises(g:ℝ)(k:ℕ)(u:Jet G):YMAt g (k+3) u↔ YMAt g (k+2) u ∧ offer k (u (k+1))= -data g (radField (k+2) u) k:=by
 constructor
 · intro h; refine ⟨reflects g u (by omega) h,?_⟩
   have he:=h k (show k+3≤k+3 from le_rfl); rw [behold g u k le_rfl,if_pos rfl] at he
   exact eq_neg_of_add_eq_zero_right he -- eq_neg orientation
 intro ⟨h,he⟩ n hn
 rw [behold g u _ (by omega)]; split
 next hk=>subst k; rw [he,add_neg_cancel]
 next h'=> rw [add_zero]; exact h _ (by omega)
lemma offer_add (k:ℕ)(p q:Taylor G (k+1)):offer k (p+q)=offer k p+offer k q:=by
 funext i; exact maxwell_add p.value q.value (fun _=> (show Good _ from Tensor.diag_smooth (p.val _) _)) (fun _=>Tensor.diag_smooth (q.val _) _) i -- defeq value pi? test
lemma offer_neg (k:ℕ)(p:Taylor G (k+1)):offer k (-p)= -offer k p:=by
 have he:=offer_add k (-p) p
 have hv:offer k (0:Taylor G (k+1))=0:=by unfold offer MaxwellOp; funext i; rw [show (0:Taylor G (k+1)).value=fun _=> (0:E4→G.Color) from (rfl : _),Finset.sum_eq_zero]; rfl; intro i hi; rw [Level.bottom (Level.zero (E:=G.Color) 0),Level.bottom (Level.zero (E:=G.Color) 0),sub_self,Level.bottom (Level.zero (E:=G.Color) 0)]
 rw [neg_add_cancel,hv] at he; exact eq_neg_of_add_eq_zero_left he.symm

/-- Stamp of coupling nonlinear completion beside the linear shell coordinates.
Define her even on inconsistent lower towers if desired; `widens` takes lawful hypothesis. -/
def raiseNext (g:ℝ)(J:Jet G)(k:ℕ): Taylor G (k+1):=
 if h:YMAt g (k+2) J then -accepted (prior g J k h) else 0
lemma widens (g:ℝ)(J:Jet G)(k:ℕ)(s:Maxwell.Shell G (k+1))(h:YMAt g (k+2) J):
    YMAt g (k+3) (update J (k+1) (raiseNext g J k + Maxwell.gaugeJet s)):=by
 let a:=raiseNext g J k + Maxwell.gaugeJet s
 let Q:=update J (k+1) a
 have he:radField (k+2) Q=radField (k+2) J:=cut (fun i hi=> update_of_ne (by omega) ..)
 change YMAt g (k+3) Q
 rw [rises, show Q (k+1)=a from update_self ..,he, offer_add,offer_shell, raiseNext, dif_pos h, offer_neg,postage,add_zero]
 rw [YMAt,he];exact ⟨h,rfl⟩ -- simp issue Q? unfolds both
end YM.RG06.ClassicalOn
