import YM.OPE.Compatible.Cum.Folly
/-!
# Bounds. Def induction coefficient cost
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier
variable {I J E R:Type}{A:Row I I}{v w:J→ℕ}{p:∀ i:J,Script I (w i+v i)}{t:Side}{d e k m n:ℕ}
variable [DecidableEq J] {s:Finset J} {α:J→ Bool}
variable {F u g y:ℝ}{r:J→ℝ}{P:Script I (e+d+1)}
-- constants common patch, versions on either s
lemma StyleK (m:ℕ)(p:Script I (e+d+1))(h:soot m p F):soot m (Shell.Temper e d p) F:= slice_fee (beginC e d) p h
lemma styleR (b:Script I (e+(d+1)+1))(hp:A.strip u y)(h:0≤u)(h':0≤ y)(hx:soot m b F)(i:Fin (d+1)): soot m (knots e d b i A) (F*y):=pad_charge hp h h' (show soot m (Shell.Cycle e d b i) F from slice_fee _ _ hx)
lemma styleM (p:Script I (e+d+1))(B:Script I (n+(k+1)))(h:soot m p F)(hp:soot m B g)(hx:A.strip u y)(he:0<u)(ha:0≤y)(i:Fin (k+1)): soot m (mitt e d n k p B i A) (F*g*(widthCost u m*y)*((3*(n+k)+2:ℕ):ℝ)^m):= slice_fee _ _ (cotton_cost hx he ha h (show soot m (orientY n k B i) g from slice_fee _ _ hp))
def coversB {I J:Type}(g h: J→ℕ)(p:∀ i:J, Script I (h i+g i))(m:ℕ)(r:J→ℝ)(s:Finset J):Prop:= ∀ i∈s,soot m (p i) (r i)
abbrev Payroll (I:Type) (u y:ℝ)(m:ℕ) (v w:J→ℕ) (s:Finset J)(d e:ℕ):Prop:=∃ B:ℝ, 0 ≤ B∧∀ A:Row I I,A.strip u y→ ∀ (α:J→Bool)(P: ∀ i:J, Script I (w i+v i))(r:J→ℝ), coversB v w P m r s→∀ p:Script I (e+d),∀ F:ℝ, soot m p F→∀ x:ℕ,soot m (Shell.Hall A v w P α s d e p x) (B*F* ∏ i∈s,r i)
-- cross branch budget after children. extract one per i
lemma crownR (s: Finset J)(i:J)(hp:i∈s)(hi:∀ d e:ℕ,Payroll I u y m v w (s.erase i) d e)(g₀ f₀:ℕ)(hu:0<u)(hv:0≤y):
   ∃ B:ℝ,0 ≤ B∧∀ A:Row I I,A.strip u y→∀ (α:J→Bool)(P: ∀ j:J,Script I (w j+v j))(r:J→ℝ),coversB v w P m r s →∀ F q,soot m q F→∀ x:ℕ,
    soot m ((if α i then Once A (Shell.Hall A v w P α (s.erase i)) f₀ g₀ q (w i) (v i) (P i) else 0: Curtain I) x) (B*F*∏ j∈s,r j):=by
       have hh (k:ℕ)(he:v i=k):∃ B:ℝ,0≤ B∧∀ A:Row I I,A.strip u y→∀ (α:J→Bool)(P:∀ j:J,Script I (w j+v j))(r:J→ℝ),coversB v w P m r s→ ∀ (p:Script I (w i+k))(hx:soot m p (r i)),∀ F q,soot m q F→∀ x:ℕ, soot m ((if α i then Once A (Shell.Hall A v w P α (s.erase i)) f₀ g₀ q (w i) k p else 0:Curtain I) x) (B*F*∏ j∈s,r j):=by
           cases k
           next => refine ⟨0,le_rfl,fun A hA α P r h p hx F q hq x=> ?_⟩;rw [zero_mul,zero_mul];split<;> exact Sack.zero le_rfl _
           next k=>
             obtain ⟨b,hb,H⟩:= hi (g₀+k) (f₀+w i); let z:=widthCost u m*y*((3*(w i+k)+2:ℕ):ℝ)^m; let D:=((k+1:ℕ):ℝ)*b*z; have hz:0≤ z:=by unfold z; have hx:= zero_le_one.trans (widthCost_ge hu m); positivity
             refine ⟨D,by unfold D; positivity,fun A hA α P r h p hx F q hq x=> ?_⟩; let X:=Shell.Hall A v w P α (s.erase i); split
             next h'=>
               let Y:= fun t:Fin (k+1)=> mitt f₀ g₀ (w i) k q p t A
               let d':=F*r i*z; let D':= b*d'*(∏ j∈s.erase i,r j)
               have ht (i:Fin (k+1)): soot m (Y i) d':=(styleM q p hq hx hA hu hv i).tips (le_of_eq (by unfold d' z;ring))
               rw [once_plus,Finset.sum_apply]; change soot m (∑ i:Fin (k+1), X _ _ (Y i) x) _; refine (Sack.finGather _ _ (fun _=>D') (fun i _=> H A hA α P r (fun k h' => h k (mem_of_mem_erase h')) _ _ (ht i) x) (fun j=>zero_le_one.trans (payer m _))).tips ?_; rw [Finset.sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; apply le_of_eq; unfold D D' d'; rw [show (∏ j∈s,r j)=r i*∏ j∈s.erase i,r j from (mul_prod_erase _ _ hp).symm];ring
             next h' => have hx:= Sack.coins hq; have hc : 0 ≤ ∏ j∈s,r j:= prod_nonneg fun i hk=>Sack.coins (h i hk); exact Sack.zero (by unfold D; positivity) _
       obtain ⟨B,hb,H⟩:=hh _ rfl; exact ⟨B,hb,fun A hA α P r h=>H A hA α P r h (P i) (h i hp)⟩
end YM.OPE.Libra.Shell
