import YM.WilsonCoeffUV.Wick.Unipotent
/-!
# Fiscal expansions and horizon-zero Wick stability to full finer limit
Prebill optional heights AFTER off-axis length.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Carp
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Soil Cosmos
open Exterior Next.Free Tree Precision Power Embroider Source Source.Drops Labels Realm PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V α:Type*} {G:Gauge}{T H P Q X:Credit} {h D i j k e n' m b N M r:ℕ}{F:Labels.Frame G h}
variable {x ξ σ A' A B y:ℝ} {s t:ℝ}
abbrev weightΩ (k:ℝ)(j:ℕ)(h:4≤j):ℝ:= max ((starFumes k h).choose) ((starLifeGap k h).choose)
lemma tolling {G:Gauge}(R:Realm G e T)(Z:Credit)(u:R.anchor≤m)(p:m≤b)(q:b≤N)(t:b≤M)(w:weightΩ R.draws.clock.kernel.penalty _ (R.draws.clock.adm m)≤R.cash Z m) :
    let A:=R.draws; let V:=sea A N m; let W:=sea A M m; let X:=R.cash (Z.prodC ((dome T).powC 2)) m; let c:=R.tempC m b; shoulder V X∧shoulder W X∧shoulder (V-W) (X*c) := by
    intro A V W X c
    let g:=A.clock.kernel.penalty; let a:=A.clock.J m; let H:=A.clock.adm m
    let C:= (starFumes g H).choose; let B:= (starLifeGap g H).choose
    have he :∀ n:ℕ,shoulder (sea A n m) C:=by
       intro n'; obtain ⟨hc,S⟩:= (starFumes g H).choose_spec; refine ⟨hc,fun x y=>?_⟩; unfold sea; obtain ⟨u,k,m'⟩:=x; obtain ⟨i,e,v⟩:= y; simp only [Matrix.of_apply]; split; · exact le_trans (Complex.abs_re_le_norm _) (S _ _ _ _).2
       rw [norm_zero]; exact hc
    have hs:=(starLifeGap g H).choose_spec.2 G A m b N M rfl p q t
    have hp : priceΩ A g m b ≤ R.cash ((dome T).powC 2) m*c:=by
       have hx : rag R.draws m b= Real.sqrt (priceΩ A g m b):=by
          unfold rag priceΩ; rw [show R.draws.S.a b / R.draws.S.a m=((location A b m).mass.val:ℝ)⁻¹ from (by rw [← mass_separation A m b p];unfold A; field_simp [(R.draws.S.a_pos b).ne']), div_eq_mul_inv]
       have hg:= R.won u p; rw [hx] at hg; have hb:0 ≤ priceΩ A g m b:= div_nonneg (Extension.UV.Linear.Dcost_pos ..).le (side_pos _).le
       calc
         _ = rag R.draws m b^2 := by rw [hx,Real.sq_sqrt hb]
         _ ≤ (R.cash (dome T) m*c)^2 := by rw [hx]; gcongr
         _ ≤ _ := by
           rw [mul_pow,cash,cash,Credit.power];  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _); rw [pow_two]; apply mul_le_of_le_one_right (Real.exp_pos _ |>.le); unfold c Realm.tempC trailC; rw [Real.exp_le_one_iff]; have hz := scales R.draws.S p; linarith
    have hQ:1≤ R.cash Z m:= Credit.purchase _ (R.depth _ u)
    have hS:B≤R.cash Z m:=(le_max_right C B).trans w
    have hv:C ≤ X:= by unfold X; rw [cash,Credit.products]; exact ((le_max_left C B).trans w).trans (le_mul_of_one_le_right (by linarith only [hQ]) (Credit.purchase _ (R.depth _ u)))
    have hz:0≤X:= (he 0).1.trans hv; have hh : 0≤c:= Real.exp_pos _ |>.le
    refine ⟨⟨hz,fun i j=> ((he N).2 i j).trans hv⟩, ⟨hz,fun i j=>((he M).2 i j).trans hv⟩, ⟨mul_nonneg hz hh,?_⟩⟩
    intro x y; obtain ⟨i,u,v⟩:= x; obtain ⟨j,s,t⟩:=y; unfold V W sea; simp only [Matrix.sub_apply,Matrix.of_apply]; split; · rw [← Complex.sub_re]; refine (Complex.abs_re_le_norm _).trans (((hs _ _ _).2).trans ?_); unfold X; rw [cash,Credit.products]; exact (mul_le_mul_of_nonneg_right hS (show 0 ≤ priceΩ A g m b from div_nonneg (Extension.UV.Linear.Dcost_pos ..).le (side_pos _).le)).trans ((mul_le_mul_of_nonneg_left hp (zero_le_one.trans hQ)).trans_eq (mul_assoc ..).symm)
    rw [sub_zero,norm_zero]; exact mul_nonneg hz hh
section costs
variable [Fintype α][NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]
lemma daystep {P Q:Gen V (Cloth α)}(p:Shelf Bank.terrain 0 s A ξ (P (r+2)) (Q (r+2)))(U W:ropes Cover α α)(h:shoulder U B)(g:shoulder W B)(v:shoulder (U-W) (B*ξ))(e:t<s)(u:0≤t): Shelf Bank.terrain 0 t (2*B*A*fareV r*tiePay α 2 (s-t)) ξ (rime U P r) (rime W Q r):= by
    have hp:=tie_nn (α:=α) (sub_pos.mpr e) 2; have hA:= p.nn; have hb:=h.1; have hh:0≤ fareV r:=by unfold fareV; positivity
    have H:B*A*fareV r*tiePay α 2 (s-t) ≤ 2*B*A*fareV r*tiePay α 2 (s-t):=by gcongr; linarith
    have hf := soul_bill h p.wax (u.trans e.le); have hG:= soul_bill g p.wane (u.trans e.le); refine ⟨(hf.meter e u).cost H,(hG.meter e u).cost H,?_⟩; rw [rime,rime,← Peb.minus hf hG (lt_of_le_of_lt u e), show rain U P r-rain W Q r=rain U (P-Q) r+rain (U-W) Q r from ?_]
    · refine ((((soul_bill h (P:=P-Q) p.toll (u.trans e.le)).add (soul_bill v p.wane (u.trans e.le))).meter e u).cost ?_); exact (le_of_eq (by unfold fareV; ring))
    funext x y; simp only [rain_spell, Pi.sub_apply, Pi.add_apply, Matrix.sub_apply, mul_sub,sub_mul,smul_sub,sub_smul]; abel
-- X^i uses increased width list.
noncomputable def loft (α:Type*)[Fintype α] (r:ℕ)(s t:ℝ)(j:ℕ):ℝ := match j with
    | 0=>1
    | i+1=> |((i+1:ℕ):ℝ)⁻¹| *(2 * loft α (r+2) s ((s+t)/2) i * fareV r * tiePay α 2 ((s+t)/2-t))
omit [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] in
lemma lo_nn (u:t<s): 0≤loft α r s t j:=by
    induction j generalizing r s t with
    | zero=> exact zero_le_one
    | succ j ih=> rw [loft]; have U : t<(s+t)/2:=by linarith
                  have hc :=tie_nn (α:=α) (sub_pos.mpr U) 2; have he:0≤ fareV r:=by unfold fareV; positivity
                  exact mul_nonneg (abs_nonneg _) (by have ht:0≤ loft α (r+2) s ((s+t)/2) j:=ih (show (s+t)/2<s from by linarith); positivity)
lemma byIvory (g:t<s)(v:0≤t){P Q:Gen V (Cloth α)} {K U:ropes Cover α α}(h:shoulder K B)(hp:shoulder U B)(he:shoulder (K-U) (B*ξ))(hq:0≤ξ)(u:Shelf Bank.terrain 0 s A ξ (P (r+2*j)) (Q (r+2*j))): Shelf Bank.terrain 0 t ((loft α r s t j)*B^j*A) ξ (ivern K P j r) (ivern U Q j r):=by
    induction j generalizing r t with
    | zero=> rw [loft,pow_zero,mul_one,one_mul]; exact (show Shelf Bank.terrain 0 _ _ _ (P r) (Q r) from u).shrink g.le
    | succ j ih=>
        have h' :0 ≤ (s+t)/2:= by linarith
        rw [show r+2*j.succ=r+2+2*j by omega] at u; have hv := (daystep (ih (by linarith : (s+t)/2<s) h' u) _ _ h hp he (by linarith : t<(s+t)/2) v).μ (((j+1:ℕ):ℝ)⁻¹); rw [loft]; exact hv.step (le_of_eq (by rw [pow_succ]; ring)) hq
lemma ivory (g:t<s)(v:0<t){P Q:Gen V (Cloth α)} {K U:ropes Cover α α}(h:shoulder K B)(hp:shoulder U B)(he:shoulder (K-U) (B*ξ))(hb:1 ≤ B)(hx:0≤ξ)(u:∀ i≤j,Shelf Bank.terrain 0 s A ξ (P (r+2*i)) (Q (r+2*i))): Shelf Bank.terrain 0 t ((∑ i∈Finset.range (j+1),loft α r s t i)*B^j*A) ξ (mason K P j r) (mason U Q j r):=by
    unfold mason; rw [Finset.sum_apply, Finset.sum_apply]
    have ha : 0 ≤ A := (u j le_rfl).nn
    apply Shelf.step (Shelf.sum _ : Shelf _ _ _ (∑ i∈Finset.range (j+1),loft α r s t i*B^i*A) ξ _ _) _ hx
    · intro i hi; exact byIvory g v.le h hp he hx (u _ (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
    rw [Finset.sum_mul,Finset.sum_mul]; apply Finset.sum_le_sum; intro i hi; apply mul_le_mul_of_nonneg_right _ ha; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) (lo_nn g)
end costs
end YM.WilsonCoeffUV.Bank.Carp
