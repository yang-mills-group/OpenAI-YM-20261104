import YM.WilsonCoeffUV.Root.Gain.Convex
import YM.Planned.PRIMARY_INTEGRAL_295.RollFilm
/-! Turning the readings around a cut. Cover positions specified.
No stationary width claim from `Whole` here. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V:Type*}{r h D l j e k:ℕ} {G:Gauge}{F:Labels.Frame G h}{s t A X Z D':ℝ}
private lemma pipes_bill (p:Fin r→ U →ℝ)(h:∀ i,Summable fun x=> ‖p i x‖): Summable fun x:Fin r→U=> ‖∏ i,p i (x i)‖ :=by
    induction r with
    | zero => exact summable_of_hasFiniteSupport (Set.toFinite _)
    | succ r ih=>
       have ht: SumBudget _ _ := (show SumBudget (fun x:U=> ‖p 0 x‖) _ from ⟨fun _=> norm_nonneg _,h 0,le_rfl⟩); let G (x:Fin r→U):= ‖∏ i:Fin r,p i.succ (x i)‖; have hu: SumBudget G _:= ⟨fun x=> norm_nonneg _,ih (fun i=> p i.succ) (fun i=> h i.succ),le_rfl⟩
       exact (cap_walk _ _ (Fin.consEquiv (fun _:Fin (r+1)=> U)) (fun i=>by rw [Fin.prod_univ_succ,norm_mul]; rfl) (prod_cap ht (cap_nn hu) fun _=> hu)).2.1
lemma pipes_cause (p: Fin r→ U→ℝ) (h:∀ i,Summable fun x=>‖p i x‖): (∑' x:Fin r→U,∏ i,p i (x i))=∏ i,∑' x,p i x:=by
   induction r with
   | zero=> rw [tsum_fintype]; simp
   | succ r ih=>
       let S:= Fin.consEquiv (fun _:Fin (r+1) => U)
       let F:= fun x:Fin (r+1)→U=>∏ i,p i (x i); let T:=F ∘ S
       have he u (b:Fin r→U): T (u,b)=p 0 u*∏ i:Fin r,p i.succ (b i):=by unfold T Function.comp F; rw [Fin.prod_univ_succ]; rfl
       rw [← S.tsum_eq F]; change tsum T=_; rw [(S.summable_iff.mpr (pipes_bill p h).of_norm).tsum_prod,Fin.prod_univ_succ]
       change (∑' u, ∑' x,T (u,x))=_; simp_rw [he,tsum_mul_left]; rw [tsum_mul_right]; exact congr_arg ((∑' i,p 0 i)*·) (ih (fun i=>p i.succ) (fun i=>h i.succ))
lemma warehouse {α:Type}[Fintype α]{F:canal Cover α (Hooks G) ℝ k r}(p:Peb Bank.terrain 0 s A F)(e:0<s)(q:Fin r→Leg G) (g:∀ i,Wages (q i)): Summable (fun i:(Fin r→YForest G)×(Fin k→Cloth α)=> ‖(∏ j,q j (i.1 j))* F i.1 i.2‖):=by
   let f (x: Fin r→YForest G):= (∏ j,q j (x j)); let Y (x:Fin r→YForest G):= Real.exp (-(s/2)*port_d 0 x); have hs : s/2<s:=by linarith
   have ht : 0<s/2:=by linarith
   have he:Twig 0 (s/2) 1 Y:= ⟨zero_le_one,fun i=>by unfold Y; rw [Real.norm_of_nonneg (by positivity),one_mul]⟩
   let W:= A*tiePay α k (s-s/2)
   let T (i:(Fin r→YForest G)×(Fin k→Cloth α)):= ‖f i.1 * F i.1 i.2‖
   have hT x: SumBudget (fun y=> T (x,y)) (‖pressOn Y q x‖*W):=by
      have he:= cap_scale (p.cache hs ht.le x) (norm_nonneg (f x)); have hx: ‖pressOn Y q x‖*W=‖f x‖*(W*Real.exp (-(s/2)*port_d 0 x)):=by rw [pressOn,norm_smul]; unfold Y f; rw [Real.norm_of_nonneg (Real.exp_pos _).le]; ring
      rw [hx]; unfold T; simp_rw [norm_mul]; exact he
   refine (summable_prod_of_nonneg (show ∀ i,0 ≤ T i from fun i=> norm_nonneg _)).mpr ⟨fun x=> (hT x).2.1, ((pluck_profit he ht g).mul_right W).of_nonneg_of_le (fun x=> tsum_nonneg fun i=>norm_nonneg _) fun i=>(hT i).2.2⟩
lemma translucent {α:Type}[Fintype α]{F:canal Cover α (Hooks G) (Vote D) k r}(p:Peb Bank.terrain 0 s A F)(e:0<s)(q:Fin r→Leg G) (g:∀ i,Wages (q i)): Summable (fun i:(Fin r→YForest G)×(Fin k→Cloth α)=> (∏ j,q j (i.1 j)) • F i.1 i.2):=by
    let T (x y):= ‖F x y‖
    have hv:Peb Bank.terrain 0 s A T:= ⟨p.1,fun x y=> by unfold T; rw [Real.norm_of_nonneg (norm_nonneg _)]; exact p.2 x y⟩
    apply Summable.of_norm; simp_rw [norm_smul]; simpa only [T,norm_mul,Real.norm_of_nonneg (norm_nonneg _)] using warehouse hv e q g
lemma pluck_pulse (P:Patch)(w:Site P.L)(Q:Drip P G)(hQ:dragCup Bank.terrain s X Q) (p:0<s)(g:s/P.L.val≤t) (Y:ChamberTen G (Vote D) r)(he:Twig 0 t A Y)(b b':Fin r→Leg G)(hb:∀ i,Wages (b i))(hb':∀ i,Wages (b' i))
    (H:∀ i y, b' i y= ∑' x, sip P Q w x y * b i x)(hx:∀ i y,Summable fun x=> ‖sip P Q w x y*b i x‖): pluck (pulseS P w Q Y) b=soprano P w D (pluck Y b'):=by
   let F:=featherS P w Y; set T:= spunk P.L F (owns P.L Q); let R (x y):= (∏ i,b i (x i)) • T x y
   let f:=uncurry R; have hv:= widget ((Cork.turn (lift w) he).touch (soprano P w D)) (fun _=>hQ) g p.le
   have hp: Summable f:= translucent hv p b hb
   rw [pulseS,patrol (L:=P.L)]
   have heq (x:Fin r→YForest G): pressOn (ruins T) b x=∑' y,f (x,y):=by rw [pressOn,ruins,←tsum_const_smul'']; rfl
   change (∑' x,pressOn (ruins T) b x)=_; simp_rw [heq, ← hp.tsum_prod];
   let M:= Equiv.prodComm (Fin r→ YForest G) (Fin r→Cloth (Co P.L (Hooks G)))
   let C:= (((Equiv.addLeft (lift w)).prodCongr (Equiv.refl (Hooks G))).trans (panel P.L (Hooks G)).symm); let W:= (Equiv.refl (Fin r)).arrowCongr C
   have hg: Summable (f ∘ M.symm):= M.symm.summable_iff.mpr hp
   rw [←M.symm.tsum_eq]; change tsum (f ∘ M.symm)=_; rw [hg.tsum_prod,← W.tsum_eq, pluck, (soprano P w D).map_tsum (pluck_profit he (lt_of_lt_of_le (div_pos p (by positivity)) g) hb').of_norm]
   refine tsum_congr fun y=>?_
   let J (i:Fin r) (x:YForest G):= sip P Q w x (y i) * b i x
   let v (x:Fin r→YForest G) i:= J i (x i); let A:= soprano P w D (Y y)
   have hz x: f (x,W y)=(∏ i,v x i) • A:=by
       unfold f uncurry R T spunk; dsimp only; unfold F featherS v J sip owns spinJob
       rw [smul_smul,Finset.prod_mul_distrib]; congr 1
       · rw [mul_comm]; congr 1; apply Finset.prod_congr rfl; intro i _; simp [W,C]; rfl
       unfold revolve A; simp only [Function.comp_apply];
       apply congr_arg (soprano P w D); apply congr_arg Y; funext j; rcases Hy:y j with ⟨k,e⟩; simp [jog,W,C,Hy]
   change (∑' x,f (x,W y))= _
   simp_rw [hz]; let L:ℝ→L[ℝ]Vote D:= (ContinuousLinearMap.id ℝ ℝ).smulRight A
   rw [show (∑' x,(∏ i,v x i) • A)= (∑' x:Fin r→YForest G,∏ i,J i (x i)) • A from Eq.symm <| L.map_tsum (pipes_bill J (fun i=>hx i _)).of_norm, pipes_cause J (fun i=>hx i _), pressOn,map_smul]; simp_rw [H]; rfl
end YM.WilsonCoeffUV.Cosmos
