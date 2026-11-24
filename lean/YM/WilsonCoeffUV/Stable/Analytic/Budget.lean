import YM.WilsonCoeffUV.Stable.Analytic.Tail
import YM.WilsonCoeffUV.Stable.PreSchedule
/-!
# Budget stages for analytic D

One appointment gives smoothing and path prep (L floors only), plus post charges at the same
gear. Existence prices quantify OVER ALL shape charts with fixed h, J neighbors,G,κ, path data.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.WilsonCoeffUV.StableStrip
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Supply Ticket Polestar Next.Foundations Real Shard Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V:Type*}{r h D l e j k a N M m b i q z u:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{A A':Levels G}
lemma establishedBefore (Ñ:ChartRatio G) (K:KernelChoices)(H:Hol G)(F:Frame G h)(p:h<D)(e k j:ℕ): ∀ᶠ L:ℕ in atTop,∀ (A:Levels G)(m:ℕ),A.clock.kernel=K → A.clock.J (m+1)=j → (A.S.block m).val=L →∀ (v:5≤ A.clock.J (m+1))(w:h+1≤ A.clock.J (m+1)-2) (l:ℕ)(u:craftQuest A m l v)(x:roomV A m v), RootPre H F p k e (liftWing Ñ w u x):=by
    -- preSpaced gives dues for all these; estimate velo directly rather than dividing by shades
    have ht a b: ∀ᶠ L:ℕ in atTop,∀ (A:Levels G)(m:ℕ), A.clock.kernel=K→ A.clock.J m=a → A.clock.J (m+1)=j → A.clock.J (m+2)=b → (A.S.block m).val=L →∀ (v:5≤ A.clock.J (m+1))(w:h+1≤ A.clock.J (m+1)-2) (l:ℕ)(u:craftQuest A m l v)(x:roomV A m v), RootPre H F p k e (liftWing Ñ w u x):=by
       by_cases hx:4≤a∧5 ≤ j∧5 ≤ b; swap; · exact Eventually.of_forall fun _ A m _ s t u _ v _ _ _ _=>False.elim (hx ⟨s ▸ A.clock.adm _,t ▸ v,u ▸ upstairs A _ v⟩)
       obtain ⟨ha,hj,hb⟩:=hx
       let U:=splash G K j b (by omega) hb; have hv:0<U:=(spatter G K j b (by omega) hb).1
       let X:=Finset.range (k+e+1); let s (r):= tempS H F r p U (saffron G K a j ha hj) (knotV G K a j ha hj) hv (safron_nn ..)
       filter_upwards [(eventually_all_finset X).mpr (fun r _=> logLane (s r)),preSpaced F H Ñ K p (k+e) j] with L h0 hL
       intro A m pK p' pJ p2 v i h l u x r t
       refine ⟨( (hL A m pK pJ v i h).2 l u x).2 r (by omega),?_⟩
       subst K a j b L; exact h0 r (Finset.mem_range.mpr (by omega))
    let S:= Finset.range (j+2)
    filter_upwards [(eventually_all_finset S).mpr (fun i _=> (eventually_all_finset S).mpr fun b _=> ht i b)] with L tL; intro A m p' x z
    have hp:= A.fits.mono (m.le_succ); have hh:A.clock.J (m+2)≤ A.clock.J (m+1)+1:= A.fits.stepSlow (m+1)
    exact tL _ (show A.clock.J m∈ S from Finset.mem_range.mpr (by change A.clock.J m≤A.clock.J (m+1) at hp; omega)) _ (show A.clock.J (m+2)∈ S from Finset.mem_range.mpr (by omega)) A m p' rfl x rfl z
lemma installed (H:Hol G)(T:SectionData F)(p:h<D)(k e:ℕ)(I:Cloister G h): ∀ᶠ z:ℝ in atTop, RootAfter H T p k e I z :=by
    filter_upwards [(eventually_all_finset (Finset.range (e+1))).mpr (fun i _=> (eventually_all_finset (Finset.range (k+e+1))).mpr fun r _=> eventually_ge_atTop (rootExpense H T p k i r I))] with z v; exact fun i t r u=> v _ (Finset.mem_range.mpr (by omega)) _ (Finset.mem_range.mpr (by omega))
lemma establishedAfter (Ñ:ChartRatio G) (K:KernelChoices) (L:Side)(H:Hol G)(T:SectionData F)(p:h<D)(k e j e':ℕ): ∀ᶠ z :ℝ in atTop,∀ (A:Levels G)(m:ℕ),A.clock.kernel=K → A.clock.J (m+1)=j → A.S.block m=L →∀ (v:5≤ A.clock.J (m+1))(w:h+1≤ A.clock.J (m+1)-2) (f:craftQuest A m e' v)(x:roomV A m v), RootAfter H T p k e (liftWing Ñ w f x) z:=by
    have hh a b: ∀ᶠ z:ℝ in atTop,∀ (A:Levels G)(m:ℕ),A.clock.kernel=K → A.clock.J (m+1)=j → A.clock.J m=a → A.clock.J (m+2)=b → A.S.block m=L →∀ (v:5≤ A.clock.J (m+1))(w:h+1≤A.clock.J (m+1)-2)(f:craftQuest A m e' v)(x:roomV A m v), RootAfter H T p k e (liftWing Ñ w f x) z:=by
       by_cases he:∃ (A:Levels G)(m:ℕ), A.clock.kernel=K ∧ A.clock.J (m+1)=j ∧ A.clock.J m=a∧ A.clock.J (m+2)=b∧ A.S.block m=L ∧∃ v:5≤A.clock.J (m+1), (h+1≤A.clock.J (m+1)-2) ∧ craftQuest A m e' v ∧ roomV A m v
       · obtain ⟨A,m,hp,hh,ha,hb,x,v,t,U,V⟩:= he; subst K a j b L
         filter_upwards [installed H T p k e (liftWing Ñ t U V)] with y hy; intro B i g h L x b w z s k; rw [←spike Ñ g L h x b t z U s V k]; exact hy
       exact Eventually.of_forall (fun c B i g h L x b w z s k=>False.elim (he ⟨B,i,g,h,L,x,b,w,z,s,k⟩))
    let S:= Finset.range (j+2)
    filter_upwards [(eventually_all_finset S).mpr (fun a _=> (eventually_all_finset S).mpr fun b _=>hh a b)] with y H'; intro A m p q l v w g x; have he:A.clock.J m≤ A.clock.J (m+1):= A.fits.mono m.le_succ; have hx:A.clock.J (m+2)≤A.clock.J (m+1)+1:= A.fits.stepSlow (m+1); exact H' _ (show A.clock.J m∈ S from Finset.mem_range.mpr (by omega)) _ (show A.clock.J (m+2)∈ S from Finset.mem_range.mpr (by omega)) A m p q rfl rfl l v w g x
variable (H) (R:Master H)
abbrev Orders (v):= Fin (v+1)× Fin (v+1) × Fin (v+1) × Fin (v+1)
private def taller (Ñ:ChartRatio G)(K:KernelChoices)(j:ℕ)(a:Orders i): ℕ:= if p:a.1.val<a.2.1.val then (eventually_atTop.mp (establishedBefore Ñ K H (R.F a.1.val) p a.2.2.2.val a.2.2.1.val j)).choose else 0
private def later (Ñ:ChartRatio G)(K:KernelChoices)(j i:ℕ)(L:Side)(a:Orders i): ℝ:= if p:a.1.val<a.2.1.val then exp (exp (eventually_atTop.mp (establishedAfter Ñ K L H (R.T a.1.val) p a.2.2.1.val a.2.2.2.val j i)).choose) else 0

def rootRise (Ñ:ChartRatio G)(K:KernelChoices)(j i:ℕ):ℕ:=∑ a:Orders i,taller H R Ñ K j a
def rootPost (Ñ:ChartRatio G)(K:KernelChoices)(j i:ℕ)(L:Side):ℝ:=∑ a:Orders i,|later H R Ñ K j i L a|
lemma onLedger (Ñ:ChartRatio G)(K:KernelChoices)(j i:ℕ)(A:Levels G)(m:ℕ) (q:A.clock.kernel=K)(g:A.clock.J (m+1)=j)(z:5≤ A.clock.J (m+1))(X:craftQuest A m i z)(Y:roomV A m z)(t:h+1≤ A.clock.J (m+1)-2) (hv:rootRise H R Ñ K j i ≤ (A.S.block m).val) (p:h<D)(hD:D≤ i)(hp:k≤ i)(he:e≤ i){B:ℝ}(hQ:rootPost H R Ñ K j i (A.S.block m) ≤ exp (exp (B-1))) : RootPre H (R.F h) p k e (liftWing Ñ t X Y) ∧ RootAfter H (R.T h) p k e (liftWing Ñ t X Y) B:=by
    let a :Orders i:= (⟨h,by omega⟩,⟨D,by omega⟩,⟨k,by omega⟩,⟨e,by omega⟩)
    have hx: a.1.val<a.2.1.val:= p
    have hP : (eventually_atTop.mp (establishedBefore Ñ K H (R.F h) p e k j)).choose ≤ rootRise H R Ñ K j i:=by
       apply le_trans _ (Finset.single_le_sum (f:=taller H R Ñ K j) (fun _ _=>Nat.zero_le _) (Finset.mem_univ a)); rw [taller,dif_pos hx]
    have hg: later H R Ñ K j i (A.S.block m) a ≤ exp (exp (B-1)):= (le_abs_self _).trans ((Finset.single_le_sum (f:=(fun i'=>|later H R Ñ K j i (A.S.block m) i'|)) (fun _ _=> abs_nonneg _) (Finset.mem_univ a)).trans hQ)
    rw [later,dif_pos hx] at hg
    exact ⟨(eventually_atTop.mp (establishedBefore Ñ K H (R.F h) p e k j)).choose_spec _ (hP.trans hv) A m q g rfl z t i X Y, (eventually_atTop.mp (establishedAfter Ñ K (A.S.block m) H (R.T h) p k e j i)).choose_spec B (redeemBill hg) A m q g rfl z t X Y⟩
end YM.WilsonCoeffUV.StableStrip
