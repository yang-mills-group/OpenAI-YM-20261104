import YM.WilsonCoeffUV.Marked.Paths.Purchase
/-!
# Assign many simultaneous loads to mixed exponential-width and renderers
Order plate. Canonical fees also optionally computed after L but BEFORE Wait.
Charges finite arity but preserve true weights/rates. Doesn't require ordering over actual panels compatible with MASK: marker log exists independent. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
-- use Fin labels, any fixed horizon.
namespace YM.WilsonCoeffUV.Wheel.Cadenza
open Wheel.Mark Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Metric Shard Realm PathCost
open Fountain Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Polestar Supply Ticket Flooring
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {ι U:Type}{G:Gauge}{F' D':ℕ →ℕ}{P:Sheet G}{Y:Supply.Rolls P}{Ω:Protection Y}{V:Delays Ω}{o:Bar V}{b':Supply.Wait o}{A:Levels G}{Ñ:ChartRatio G}{i k b h l e:ℕ}{D X:ι→ℕ}
section
variable [Fintype ι][DecidableEq ι]
lemma insuredAll (H:Hol G)(M:Master H)(u:∀ i,X i<D i)(g:G.Simple)(q:LocalRatio Ñ) (pL:floors G P.kernel F' ≤ P.floorL)(zL:(fun i=>sharp H M P.kernel Ñ i (F' i) (D' i))≤ P.floorL)(zS:preBoard P F'≤ P.floorL)(a:Paid b' A)(s:Ticket.voucher Y F' Ñ≤ V.betaEntry)(x:(fun j=>tickZ H M P.kernel Ñ (Y.L j) (F' j) (D' j) j)≤ V.betaEntry) (v:ℕ→Gear G →ℝ)(hY: coolTax F' P Y Ñ v ≤ V.betaEntry)
   (t:∀ j≥i, let k:= A.clock.J (j+1); let n:=F' k; 5 ≤ k ∧ e+1 ≤ n ∧ (∀ s:ι,X s+1≤ k-2 ∧ D s ≤ D' k) ∧ censusV G D X b h e≤ v n):
   ∃ T: Realm G (e+1) Credit.leanC, T.draws=A∧ T.paid=Ñ∧T.y=zz A∧T.anchor=i∧ Cloze D X T Credit.leanC∧ Insure b h T Credit.leanC ∧ Nonempty (Tribe T H Credit.leanC Credit.leanC (counter H M X D u))∧ ∀ j(hb:i≤j)(p:T.anchor≤j), (T.mint j p).σ=crestM A j (t j hb).1 ∧ v (F' (A.clock.J (j+1))) (T.mint j p).gear ≤ T.cash Credit.leanC j:=by
   obtain ⟨N,hN⟩:= Venice (e:=e+1) a i (fun j p=>⟨(t j p).1,(t j p).2.1⟩) v zS hY
   obtain ⟨hx,ht,_⟩:= install_awards g q pL a s i (e+1) (fun j p=>⟨(t j p).1,(t j p).2.1⟩)
   let T: Realm G (e+1) Credit.leanC:= ⟨A,Ñ,g,q,i, zz A,hx,ht,N.mass,N.overlap, fun i v=> by rw [Credit.lean_cost]; exact N.takes i v⟩
   have he j (p:T.anchor≤ j): (T.mint j p).σ=crestM A j (t j p).1∧v (F' (A.clock.J (j+1))) (T.mint j p).gear ≤ T.cash Credit.leanC j:= by rw [cash,Credit.lean_cost]; exact ⟨(hN j p).2,(hN j p).1⟩
   have hu j (p:T.anchor≤ j): tellerR G D X e (T.mint j p).gear ≤ T.cash Credit.leanC j∧ stow G h b (e+1) (T.mint j p).gear ≤ T.cash Credit.leanC j:= max_le_iff.mp (le_trans ((t j p).2.2.2 _) (he j p).2)
   refine ⟨T,rfl,rfl,rfl,rfl,⟨fun j p=>(max_le_iff.mp (show max _ _ ≤_ from (hu j p).1)).1,fun j p=>(max_le_iff.mp (show max _ _ ≤ _ from (hu j p).1)).2⟩, insured b h T (fun j p=>(hu j p).2),⟨fun y=>?_⟩,fun j _ p=> he j p ⟩
   apply Classical.choice; obtain ⟨Y,hM,x',y',f,c⟩:= fixtures_paid H M g q pL zL a s x (u y) e i (fun j v=> ⟨(t j v).1,((t j v).2.2.1 y).1,(t j v).2.1,((t j v).2.2.1 y).2⟩)
   let P :PassportC H T (counter H M X D u y) Credit.leanC Credit.leanC:= ⟨Y,hM,x',y',f⟩
   refine ⟨P,fun j v=>?_⟩; obtain ⟨p,b,x,t',g⟩:= c j (f.symm ▸ v); rw [(he j v).1,show P.f.arch.angle j _ =_ from g]; exact le_rfl
end

def diary (G:Gauge)(L:ℕ)(I:Gear G): ℝ := ∑ i:Fin (L+1),∑ b: Fin (L+1),∑ h: Fin (L+1),∑ e:Fin (L+1),∑ D: Fin i.val→Fin (L+1),∑ k:Fin i.val→ Fin (L+1), |censusV G (fun j=>(D j).val) (fun j=>(k j).val) b h e I|

lemma depot (G:Gauge) (L i b h e:ℕ)(D k:Fin i→ℕ)(p:i≤L)(v:b≤L)(x:h≤ L)(z:e≤ L)(H:∀ j,D j≤ L)(u:∀ j,k j≤ L): censusV G D k b h e ≤ diary G L:=by
   classical
   let V:=Fin (L+1); let i':V:=⟨i,by omega⟩; let b':V:=⟨b,by omega⟩; let h':V:=⟨h,by omega⟩; let e':V:=⟨e,by omega⟩; let D':Fin i→V:=fun j=> ⟨D j,Nat.lt_succ_of_le (H j)⟩; let k':Fin i→V:=fun j=>⟨k j,Nat.lt_succ_of_le (u j)⟩
   intro S; refine le_trans (le_abs_self _) ?_; unfold diary
   apply le_trans _ (Finset.single_le_sum _ (Finset.mem_univ i'))
   · apply le_trans _ (Finset.single_le_sum _ (Finset.mem_univ b'))
     · apply le_trans _ (Finset.single_le_sum _ (Finset.mem_univ h'))
       · apply le_trans _ (Finset.single_le_sum _ (Finset.mem_univ e'))
         · apply le_trans _ (Finset.single_le_sum _ (Finset.mem_univ (D':Fin i'.val→Fin (L+1))))
           · exact Finset.single_le_sum (f:=fun f:Fin i'.val→Fin (L+1)=> |censusV G (fun j=> (D' j).val) (fun j=> (f j).val) b h e S|) (fun f _=> abs_nonneg _) (Finset.mem_univ k')
           intro i _; positivity
         intro i _; positivity
       intro i _; positivity
     intro i _; positivity
   intro i _; positivity

lemma maturity {i' h': Fin l→ℕ}(H:Hol G)(M:Master H)(u:∀ i,i' i<h' i)(g:G.Simple)(q:LocalRatio Ñ)
    (pL:floors G P.kernel F' ≤ P.floorL)(zL:(fun i=>sharp H M P.kernel Ñ i (F' i) (F' i))≤ P.floorL)
    (zS:preBoard P F'≤ P.floorL)(a:Paid b' A)(s:Ticket.voucher Y F' Ñ≤ V.betaEntry)(x:(fun j=>tickZ H M P.kernel Ñ (Y.L j) (F' j) (F' j) j)≤ V.betaEntry)
    (v:ℕ→Gear G →ℝ)(hY: coolTax F' P Y Ñ (diary G⊔ v) ≤ V.betaEntry) (y:Tendsto F' atTop atTop)(b h e:ℕ): ∀ᶠ i:ℕ in atTop,
    ∃ T: Realm G (e+1) Credit.leanC, T.draws=A∧ T.paid=Ñ∧T.y=zz A∧T.anchor=i∧ Cloze h' i' T Credit.leanC
    ∧ Insure b h T Credit.leanC ∧ Nonempty (Tribe T H Credit.leanC Credit.leanC (counter H M i' h' u))
    ∧ ∀ j(_:i≤j)(t:T.anchor≤j), ∃ z:5≤A.clock.J (j+1), (T.mint j t).σ=crestM A j z ∧ v (F' (A.clock.J (j+1)))
    (T.mint j t).gear ≤ T.cash Credit.leanC j:= by
   have he:Tendsto (fun i=>A.clock.J (i+1)) atTop atTop:=A.fits.deep.comp (tendsto_add_atTop_nat 1); let f:= F' ∘ fun i => A.clock.J (i+1); have hp:Tendsto f atTop atTop:=y.comp he
   obtain ⟨L,t⟩:= (eventually_atTop.mp ((he.eventually_ge_atTop 5).and ((hp.eventually_ge_atTop (b+h+e+1+l)).and (eventually_all.mpr fun j:Fin l=> (he.eventually_ge_atTop (i' j+3)).and (hp.eventually_ge_atTop (h' j)))))); apply (eventually_ge_atTop L).mono; intro i p
   have hh : ∀ j ≥ i, let k:= A.clock.J (j+1); let n:=F' k; 5 ≤ k ∧ e+1≤ n ∧ (∀ s:Fin l,i' s+1≤k-2∧ h' s≤ n) ∧ censusV G h' i' b h e ≤ (diary G⊔v) n :=by
     intro j v'; let N:= A.clock.J (j+1); obtain ⟨hV,z,d⟩:= t j (p.trans v'); dsimp only [f,Function.comp_apply] at z d; refine ⟨hV,by omega,fun q=>by specialize d q; omega,?_⟩
     exact le_trans (depot G (F' N) l b h e h' i' (by exact le_trans (Nat.le_add_left ..) z) (by unfold N; omega) (by unfold N; omega) (by unfold N; omega) (fun i => (d i).2) (fun j=> (u j).le.trans (d j).2)) (le_sup_left (b:=v (F' N)))
   obtain ⟨T,h₁,h₂,h₃,h₄,t1,t2,t3,t4⟩:= insuredAll H M u g q pL zL zS a s x (e:=e) (i:=i) _ hY (b:=b) (h:=h) hh
   refine ⟨T,h₁,h₂,h₃,h₄,t1,t2,t3,fun j p t=>?_⟩; have h₀:=t4 j p t; exact ⟨_,h₀.1,le_trans (le_max_right ..) h₀.2⟩
end YM.WilsonCoeffUV.Wheel.Cadenza
