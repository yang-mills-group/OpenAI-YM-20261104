import YM.OPE.Compatible.Kiosk.Rain
/-! # TransformK colors and accounts. Norm coherence and branch. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Votive
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Flume Flume.Script Frequency
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{n c f L:Side}{P:Patch}{K:KernelChoices}{I J M:Type}{m k r d:ℕ}{σ C s u z:ℝ}{B:Sponsor G} {H:Seasons B}{V:ChartRatio G}{p:Clip}
namespace Alps
open Page Virgin Planned.PrimaryIntegral295.Carrier Boxes Roles
lemma paysForward {W:TileC H P p V C → Script I r}(h: Wcap H P p V C m W): Wcap H P p V C m (W ∘ fallsF):=by
    obtain ⟨a,b,n,H⟩:=h; refine ⟨a,b,n,fun i=>(H (fallsF i)).tips ?_⟩; have h : downK (fallsF i)≤ downK i:=pow_le_pow_of_le_one (by norm_num :0 ≤ (1/2:ℝ)) (by norm_num) (Nat.le_succ i.2); change a*upperX i ^ n *_ ≤ _; exact mul_le_mul_of_nonneg_left h (mul_nonneg b (zero_le_one.trans (one_le_pow₀ (le_trans i.1.1.fits (le_max_left ..)))))
lemma foldPay {q:TileC H P p V C→Script I r}(hs: Loan m q 1 upperX) {K:TileC H P p V C→ ℝ}(hk:Penny H P p V C K): Wcap H P p V C m (fun i=> K i • q i):=by
   obtain ⟨a,b,n,Hq⟩:= hs; obtain ⟨c,hc,d,hD⟩:=hk; refine ⟨c*a,mul_nonneg hc b,d+n,fun i=>((Hq i).scale_line (K i)).tips ?_⟩; simp only [Pi.one_apply,mul_one]; apply (mul_le_mul_of_nonneg_right (hD i) (mul_nonneg b (pow_nonneg (zero_le_one.trans (max_cap _ _ _ _ _ i)) n))).trans_eq; ring
lemma driftPaid (U0:Tall (H:=H) (P:=P) (p:=p) (V:=V) (C:=C) 2 m) (hk:Penny H P p V C (betaA-betaE)): Wcap H P p V C m driftQ:=by
    let x :TileC H P p V C →Script (Shade G) 2:=dayV 2∘fallsF; have ht :Loan m x 1 upperX:= word_loan p (fun i:TileC H P p V C=> VA (fallsF i)) fun i=> (fallsF i).1.2.R _
    let y:= (marksD (H:=H) (P:=P) (V:=V) (p:=p) (C:=C) 2) ∘ fallsF; have hT: Wcap H P p V C m (fun i=>betaA i • y i):=by
       obtain ⟨a,ha,n,A⟩:= paysForward U0; refine ⟨max C 0*a,mul_nonneg (le_max_right ..) ha,n,fun i=>((A i).scale_line (betaA i)).tips ?_⟩; apply (mul_le_mul_of_nonneg_right ((i.1.1.bound _).trans (le_max_left ..)) (A i).coins).trans_eq; ring
    have hh:= Loan.seize hT (foldPay ht hk) (max_cap (P:=P) (p:=p) (H:=H) (V:=V) (C:=C)) (fun i=> pow_nonneg (by norm_num : 0 ≤ (1/2:ℝ)) _ ); rw [show driftQ= _ from ?_]; exact hh
    ext1 i; let a:=dayU 2 (fallsF i); let b:=dayV 2 (fallsF i); change betaA i • a-betaE i • b= betaA i • (a-b)+(betaA i-betaE i) • b; rw [smul_sub,sub_smul]; abel
lemma energyProd (hv : LocalRatio V)(hh: Crest G P B.K m) (h:G.Simple) :
    let H! : TileC H P p V C→ℝ := betaA-betaE
    (∀ t,0 < t→ t ≤ 4→ Tall (H:=H) (P:=P) (C:=C) (p:=p) (V:=V) t m) ∧ Penny H P p V C H! ∧ Wcap H P p V C m (Newton 2):=by
      intro H!
      obtain ⟨T⟩:= medal_buy (G:=G) P.odd_side (B.affordable P) P.order_cut; obtain ⟨t,F,hp,hF,hQ⟩:= running H P T p V C hh
      have hf :Tall (H:=H) (P:=P) (V:=V) (p:=p) (C:=C) 1 m:=by
          suffices he: (marksD (H:=H) (P:=P) (p:=p) (V:=V) (C:=C) 1) =0 by unfold Tall; rw [he]; exact Loan.zero ..
          ext1 i; change (UA i).word _- (VA i).word _=0; rw [(UA i).soft_word h,(VA i).soft_word h,sub_self]
      have h₂:Tall (H:=H) (P:=P) (C:=C) (p:=p) (V:=V) 2 m:=by
          obtain ⟨a,ha,n,A⟩:=hQ; let c:ℝ:=Fintype.card (Ink (Shade G) 2)*widthCost t m; have hc:0 ≤ c:= mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans (widthCost_ge hp m)); refine ⟨c*a,mul_nonneg hc ha,n,fun i=> ((UA i).textBudget (VA i) (A i) P.order_cut hp (mul_nonneg (mul_nonneg ha (pow_nonneg (zero_le_one.trans (max_cap ..)) _)) (hF.tune i).le) m).tips (le_of_eq ?_) ⟩; unfold c; ring
      have h1 (i:ℕ)(hi:i <3)(hx:0 < i) :Tall (H:=H) (P:=P) (C:=C) (p:=p) (V:=V) i m:=by interval_cases i; exact hf; exact h₂
      have h3:= luckThree hF hv hh h1; have hx (i:ℕ)(hi:i < 4)(hz:0 < i): Tall (H:=H) (P:=P) (C:=C) (p:=p) (V:=V) i m:=by
          by_cases h:i <3; exact h1 i h hz
          rwa [show i=3 from by omega]
      have h4:= luckFour hF hv hh hx; have ht:= tempo hF h hv h3 h4; have hb:= centaur h hh.mark ht
      refine ⟨fun i hv he=> ?_,hb,?_⟩
      · by_cases h:i=4; subst i; exact h4
        exact hx i (by omega) hv
      obtain ⟨hU,hV⟩ := LeafLoan (P:=P) (p:=p) (H:=H) (V:=V) (C:=C) (m:=m) (r:=2); let K:=(Newton (H:=H) (P:=P) (C:=C) (p:=p) (V:=V) 2); apply onWheels (H:=H) (p:=p) (V:=V) (C:=C) P K bramble m (hU.debit hV hF.fuel zero_le_one); swap
      · intro i c hp; have ht(i:TileC H P p V C):=((UA i).pollbb (n:=1) (by omega)); have hq: (K i).pinned:= ((stint_cut _ _ _ _ ((UA i).fullL 2) ((VA i).fullL 2)).sym 2).1; apply hh.Bi (UA i).gear (K i) c hp _ hq; exact Poll_diff _ _ (ht i) ((VA i).pollbb (n:=1) (by omega)) (((UA i).fullL 2).here _) (((VA i).fullL 2).here _)
      rw [show K ∘ fallsF - bramble= yesterday-driftQ from ?_]; exact Loan.debit ht (driftPaid h₂ hb) hF.fuel fun i=> (hF.tune i).le
      ext1 i; change K (fallsF i)-_= (K _+ driftQ i-bramble i)- _; abel -- elabor fix
end Alps
end YM.OPE.Votive
