import YM.WilsonCoeffUV.Stable.WickRead
/-!
# Block/halo budget actual. L chosen before all cuts in quote. Can append any family of pre/post boosts of the same pattern. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.WilsonCoeffUV.Shard.Plan
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Supply Ticket Polestar Next.Foundations Real
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V:Type*}{r h D l e j k a N M m b i q z u:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{A A':Levels G}
-- prenexus formulas. true width independence from shape. reserve ℓ one more than actually possible.
def preb (H: Hol G)(F:Frame G h)(p:h<D)(_v:Rails h k u e)(C:Cloister G h): Prop:= ∀ r,r≤k+e → permeability H F p u r C.lamp/(inkPin C).patch.L.val ≤ exp (-log (inkPin C).patch.L.val/2)
lemma logLane (C:ℝ): ∀ᶠ L:ℕ in atTop,C/L≤ Real.exp (-Real.log L/2):=by
    have H: Tendsto (fun L:ℕ=>Real.exp (Real.log L/2)) atTop atTop := Real.tendsto_exp_atTop.comp (Tendsto.atTop_div_const (by norm_num) (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
    filter_upwards [H.eventually_ge_atTop C,eventually_gt_atTop 0] with L h hL; rw [div_le_iff₀ (by positivity)]
    refine h.trans_eq ?_; nth_rw 3 [← Real.exp_log (show 0<(L:ℝ) by positivity)]; rw [←Real.exp_add]; congr 1; ring
lemma begun (H: Hol G)(F:Frame G h)(p:h<D)(v:Rails h k u e)(Ñ:ChartRatio G)(K:KernelChoices)(j:ℕ): ∀ᶠ L:ℕ in atTop,∀ (A:Levels G)(m:ℕ), A.clock.kernel=K → A.clock.J (m+1)=j → (A.S.block m).val=L → ∀ (b:5≤ A.clock.J (m+1)) (w:h+1≤ A.clock.J (m+1)-2) (l:ℕ)(u:craftQuest A m l b)(x:roomV A m b), preb H F p v (liftWing Ñ w u x):=by
    have ht i: ∀ᶠ L:ℕ in atTop,∀ (A:Levels G)(m:ℕ), A.clock.kernel=K → A.clock.J (m+1)=j → A.clock.J m=i → (A.S.block m).val=L → ∀ (b:5≤ A.clock.J (m+1)) (w:h+1≤ A.clock.J (m+1)-2) (l:ℕ)(u:craftQuest A m l b)(x:roomV A m b), preb H F p v (liftWing Ñ w u x):=by
       by_cases he:4≤ i∧5≤ j; swap; · exact Eventually.of_forall fun L A m g h v t b _ _ _ _=> False.elim (he ⟨v ▸ A.clock.adm _, h ▸ b⟩)
       obtain ⟨hi,hj⟩:=he; let y:= knotV G K i j hi hj; let s:= saffron G K i j hi hj; have hs:0<s:= safron_nn G K i j hi hj
       let V (r:ℕ):ℝ:=if h':r≤k+e then PrivCost F H p u r v.rung (v.read h') y s hs else 0
       let S:= Finset.range (k+e+1); filter_upwards [(eventually_all_finset S).mpr (fun i _=> logLane (V i))] with L hL; intro A m b a t g c w l u x r q
       subst K j i L; have H':= hL r (Finset.mem_range.mpr (by omega)); unfold V at H'; rw [dif_pos q] at H'; unfold permeability; rw [dif_pos (show _ from ⟨v.rung,v.read q⟩)]; exact H'
    filter_upwards [(eventually_all_finset (Finset.range (j+1))).mpr (fun i _=> ht i)] with L h; intro A m p x; apply h (A.clock.J m) ?_ A m p x rfl; exact Finset.mem_range.mpr (Nat.lt_succ_of_le (x ▸ A.fits.mono (Nat.le_succ m)))
lemma supports (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(I:Cloister G h): ∀ᶠ z:ℝ in atTop, preb H F p v I → CompassP H T p v I z:=by
    let E:=Finset.range (e+1); let S:= Finset.range (k+e+1)
    have he (a i:ℕ): ∀ᶠ z:ℝ in atTop,∀o:i≤k+e, Daunt H T p v a i o I≤z:=by
       by_cases h:i≤k+e; · exact (eventually_ge_atTop (Daunt H T p v a i h I)).mono fun _ g t=>g
       exact Eventually.of_forall (fun i t=> False.elim (h t))
    filter_upwards [(eventually_all_finset E).mpr (fun a _=> (eventually_all_finset S).mpr fun i _=> he a i),(eventually_all_finset E).mpr (fun a _=> (eventually_all_finset S).mpr fun i _=> eventually_ge_atTop (Cans F T p v a i (inkPin I)))] with x t y; exact fun v=> ⟨v,fun i r e t'=>t _ (Finset.mem_range.mpr (by omega)) _ (Finset.mem_range.mpr (by omega)) t',fun i r e t=>y _ (Finset.mem_range.mpr (by omega)) _ (Finset.mem_range.mpr (by omega))⟩
lemma slotLease (Ñ:ChartRatio G) (K:KernelChoices) (L:Side)(H:Hol G)(T:SectionData F)(p:h<D)(u:Rails h k u e)(j e':ℕ): ∀ᶠ z :ℝ in atTop,∀ (A:Levels G)(m:ℕ),A.clock.kernel=K → A.clock.J (m+1)=j → A.S.block m=L →∀ (v:5≤ A.clock.J (m+1))(w:h+1≤ A.clock.J (m+1)-2) (f:craftQuest A m e' v)(x:roomV A m v), preb H F p u (liftWing Ñ w f x) → CompassP H T p u (liftWing Ñ w f x) z:=by
    have hh a b: ∀ᶠ z:ℝ in atTop,∀ (A:Levels G)(m:ℕ),A.clock.kernel=K → A.clock.J (m+1)=j → A.clock.J m=a → A.clock.J (m+2)=b → A.S.block m=L →∀ (v:5≤ A.clock.J (m+1))(w:h+1≤A.clock.J (m+1)-2)(f:craftQuest A m e' v)(x:roomV A m v),preb H F p u (liftWing Ñ w f x) → CompassP H T p u (liftWing Ñ w f x) z:=by
       by_cases he:∃ (A:Levels G)(m:ℕ), A.clock.kernel=K ∧ A.clock.J (m+1)=j ∧ A.clock.J m=a∧ A.clock.J (m+2)=b∧ A.S.block m=L ∧∃ v:5≤A.clock.J (m+1), (h+1≤A.clock.J (m+1)-2) ∧ craftQuest A m e' v ∧ roomV A m v
       · obtain ⟨A,m,hp,hh,ha,hb,x,v,t,U,V⟩:= he; subst K a j b L
         filter_upwards [supports H T p u (liftWing Ñ t U V)] with y hy; intro B i g h L x b w z s k; rw [←spike Ñ g L h x b t z U s V k]; exact hy
       exact Eventually.of_forall (fun c B i g h L x b w z s k W=>False.elim (he ⟨B,i,g,h,L,x,b,w,z,s,k⟩))
    let S:= Finset.range (j+2)
    filter_upwards [(eventually_all_finset S).mpr (fun a _=> (eventually_all_finset S).mpr fun b _=>hh a b)] with y h; intro A m p q l v w g x; have he:A.clock.J m≤ A.clock.J (m+1):= A.fits.mono m.le_succ; have hx:A.clock.J (m+2)≤A.clock.J (m+1)+1:= A.fits.stepSlow (m+1); exact h _ (show A.clock.J m∈ S from Finset.mem_range.mpr (by omega)) _ (show A.clock.J (m+2)∈ S from Finset.mem_range.mpr (by omega)) A m p q rfl rfl l v w g x

-- combine ledger families; use all demands h,D,e,k,u request sizes ≤F_j aux(now use F' for every). Use `paid b boost`.
variable (H) (R:Master H)
abbrev Abbey (v):= Fin (v+1)× Fin (v+1) × Fin (v+1) × Fin (v+1) × Fin (v+1)
private def climbsB (Ñ:ChartRatio G)(K:KernelChoices)(j:ℕ)(a:Abbey m): ℕ:=by
    classical
    exact if H0:a.1.val<a.2.1.val ∧ Rails a.1.val a.2.2.2.1.val a.2.2.2.2.val a.2.2.1.val then (eventually_atTop.mp (begun H (R.F a.1.val) H0.1 H0.2 Ñ K j)).choose else 0

def climbP (Ñ:ChartRatio G)(K:KernelChoices)(j m:ℕ):ℕ:= ∑ a:Abbey m, climbsB H R Ñ K j a
private def holdBar (Ñ:ChartRatio G)(K:KernelChoices)(j m:ℕ)(L:Side)(a:Abbey m): ℝ:=by
    classical
    exact if H0:a.1.val<a.2.1.val∧Rails a.1.val a.2.2.2.1.val a.2.2.2.2.val a.2.2.1.val then exp (exp (eventually_atTop.mp (slotLease Ñ K L H (R.T a.1.val) H0.1 H0.2 j m)).choose) else 0

def guardRail (Ñ:ChartRatio G)(K:KernelChoices)(j m:ℕ)(L:Side):ℝ:= ∑ i:Abbey m, |holdBar H R Ñ K j m L i|

structure Demesne (x y:ℕ): Prop where
    pace : x≤y
lemma PackingCash (Ñ:ChartRatio G)(K:KernelChoices)(j i:ℕ)(A:Levels G)(m:ℕ) (q:A.clock.kernel=K)(g:A.clock.J (m+1)=j)(z:5≤ A.clock.J (m+1))(X:craftQuest A m i z)(Y:roomV A m z)(t:h+1≤ A.clock.J (m+1)-2) (hv:climbP H R Ñ K j i ≤ (A.S.block m).val) (p:h<D)(v:Rails h k u e)(hD:D≤ i)(hp:k≤ i)(hu:u ≤ i)(he:e≤ i){B:ℝ}(hQ:guardRail H R Ñ K j i (A.S.block m) ≤ exp (exp (B-1))) : CompassP H (R.T h) p v (liftWing Ñ t X Y) B:=by
    classical
    let a :Abbey i:= (⟨h,by omega⟩,⟨D,by omega⟩,⟨e,by omega⟩,⟨k,by omega⟩,⟨u,by omega⟩)
    have hx: a.1.val<a.2.1.val∧Rails a.1.val a.2.2.2.1.val a.2.2.2.2.val a.2.2.1.val:= ⟨p,v⟩
    have hP : (eventually_atTop.mp (begun H (R.F h) p v Ñ K j)).choose ≤ climbP H R Ñ K j i:=by
       apply le_trans _ (Finset.single_le_sum (f:=climbsB H R Ñ K j) (fun _ _=>Nat.zero_le _) (Finset.mem_univ a)); rw [climbsB,dif_pos hx]
    have hg: holdBar H R Ñ K j i (A.S.block m) a ≤ exp (exp (B-1)):= (le_abs_self _).trans ((Finset.single_le_sum (f:=(fun i'=>|holdBar H R Ñ K j i (A.S.block m) i'|)) (fun _ _=> abs_nonneg _) (Finset.mem_univ a)).trans hQ)
    rw [holdBar,dif_pos hx] at hg
    exact (eventually_atTop.mp (slotLease Ñ K (A.S.block m) H (R.T h) p v j i)).choose_spec B (redeemBill hg) A m q g rfl z t X Y ((eventually_atTop.mp (begun H (R.F h) p v Ñ K j)).choose_spec _ (hP.trans hv) A m q g rfl z t i X Y)
lemma Packing (Ñ:ChartRatio G)(K:KernelChoices)(j i:ℕ)(A:Levels G)(m:ℕ) (q:A.clock.kernel=K)(g:A.clock.J (m+1)=j)(z:5≤ A.clock.J (m+1))(X:craftQuest A m i z)(Y:roomV A m z)(t:h+1≤ A.clock.J (m+1)-2) (hv:climbP H R Ñ K j i ≤ (A.S.block m).val) (p:h<D)(v:Rails h k u e)(hD:D≤ i)(hp:k≤ i)(hu:u ≤ i)(he:e≤ i)(hQ:guardRail H R Ñ K j i (A.S.block m) ≤ A.clock.hatBeta m) : CompassP H (R.T h) p v (liftWing Ñ t X Y) (zz A m):=by
    exact PackingCash H R Ñ K j i A m q g z X Y t hv p v hD hp hu he (hQ.trans_eq (scaledBills A m))
end YM.WilsonCoeffUV.Shard.Plan
