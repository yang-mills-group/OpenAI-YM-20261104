import YM.MSbar.Ballet.Card
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Ballet
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Parma Tin Bronze Asymptotics Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Alto Mosaic Mosaic.Issue
variable {G:Gauge}
open Heath Stock -- Hunger Horizon conflict. 
variable (O:ChartRatio G)(K:MapPrices)(p s m:ℕ)(j i:ℕ)(H H':Stage)(P:Patch)(X:KernelChoices)(B:Uniform.Before G H'.width H'.paths j X (p+3)) (u:G.ColorIndex)(W:Voice G)
open Supply Input Push.PriceCompiler
structure Load (K:MapPrices)(X:KernelChoices)(O:ChartRatio G)(A:Levels G)(u:G.ColorIndex)(Z:Voice G):Prop where
    pay (j i s p m:ℕ) : let g:= A.clock.J (j+1); 6 ≤ s → s ≤ g →4 ≤ m→ m ≤ g → p+2 ≤ m → (A.clock.op j i).patch.Branches X G → ∃ (B:Uniform.Before G (A.params (j+1)).width (A.params (j+1)).paths g X (p+3)),Sent O K p s m g (A.clock.J j) (A.params j) (A.params (j+1)) (A.clock.op j i).patch X B u Z (A.clock.hatBeta j)
variable {Y:Sheet G}{R:Rolls Y}{Q:Protection R}(D:Delays Q)(hG:G.Simple)(hχ:LocalRatio O)(hp:∀i:ℕ,Prepared K i (R.L i) G)(hs:Clear G W)
include hG hχ hp hs
lemma tenor (d:ℕ): ∀ᶠ x:ℝ in atTop,∀ s ≤ d,∀ m ≤ d,∀ p ≤ d,∀ i ≤ d,6 ≤ s →4 ≤ m →p+2 ≤ m →∀ P:Patch,P.J=d→P.L=R.L d→P.Branches Y.kernel G →∃ B, Sent O K p s m d i (Y.profile i) (Y.profile d) P Y.kernel B u W x:=by
    by_cases hd:4 ≤ d
    · let P:Patch:= ⟨R.L d,d,hd,(R.large d).size,(R.large d).odd⟩
      have hx(s m p i:ℕ)(hW:s ≤ d)(hm:m ≤ d)(h:p ≤ d)(hh:i ≤ d):∀ᶠ x:ℝ in atTop, 6 ≤ s →4 ≤ m →p+2 ≤ m→ P.Branches Y.kernel G →∃ B,Sent O K p s m d i (Y.profile i) (Y.profile d) P Y.kernel B u W x:=by
           by_cases hS : 6 ≤ s ∧4 ≤ m ∧p+2 ≤ m∧P.Branches Y.kernel G
           · obtain ⟨T⟩:=pre_order G (Y.profile d).width (Y.profile d).paths d Y.kernel (n:=p+3) (by omega)
             exact (card O K p s m d i (Y.profile i) (Y.profile d) P Y.kernel T u W hG hχ (hp d) hS.1 hm hS.2.2.1 hS.2.1 hW hh hS.2.2.2 rfl hs).mono (fun x he _ _ _ _=>⟨T,he⟩)
           exact Eventually.of_forall fun x i j k hu=>(hS ⟨i,j,k,hu⟩).elim
      let f:=Finset.range (d+1); have hr(k:ℕ): k∈f↔k ≤ d:=mem_range.trans Nat.lt_succ_iff
      filter_upwards [f.eventually_all.mpr (fun i hi=>f.eventually_all.mpr fun j hj=> f.eventually_all.mpr fun k hk=> f.eventually_all.mpr fun z hz=>hx _ _ _ _ ((hr _).mp hi) ((hr _).mp hj) ((hr _).mp hk) ((hr _).mp hz))] with t ht i he j hj k hk z hz hK hJ hk' P' he' hT; have hf:P'=P:=by cases P'; unfold P; congr
      rw [hf]; exact ht _ ((hr _).mpr he) _ ((hr _).mpr hj) _ ((hr _).mpr hk) _ ((hr _).mpr hz) hK hJ hk'
    exact Eventually.of_forall (fun x _ hu m _ _ _ _ _ hv hr he P he'=> (hd (he' ▸ P.order_cut)).elim)
lemma stage :∃ V:Delays Q,DelayLe D V∧∀ V':Delays Q,DelayLe V V'→∀ (B:Bar V')(w:Wait B)(A:Levels G),Paid w A→Load K Y.kernel O A u W:=by -- namespace?
   choose f hf using fun n:ℕ=>eventually_atTop.mp (tenor O K u W hG hχ hp hs n); let V:Delays Q:={D with betaEntry:=fun i=>max (D.betaEntry i) (f i)}
   refine ⟨V,⟨fun j=>le_max_left ..,le_rfl,le_rfl,le_rfl⟩,fun V' hh B w A he=>?_⟩; constructor; intro j i s p m g hS hv hm hz hP hk
   let n:= A.clock.op j i; let J:= n.patch.J; let i' := A.clock.J j
   have hξ(m):A.params m= Y.profile (A.clock.J m):= by unfold Levels.params Calendar.params; rw [he.stage]
   rw [hξ _,hξ _]
   have hz:max p m ≤ g:=max_le (by omega) hz
   refine hf J (A.clock.hatBeta j) ((le_max_right (D.betaEntry J) _).trans ((hh.beta g).trans (he.pays j))) s hv m ?_ p ?_ i' (A.fits.mono (Nat.le_succ _)) hS hm hP n.patch rfl ?_ hk; exact (le_max_right ..).trans hz; exact (le_max_left ..).trans hz; change A.S.block j= R.L g; rw [← A.fits.sameFactor, he.lengths]
end YM.MSbar.Ballet
