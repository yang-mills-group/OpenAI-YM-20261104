import YM.LocalLTE.FieldPT.Root
/-!
 ETCHED payload billed from true Lifetime. This is a LOCAL convention:
 grade interpreted as a prescribed normalization `grain`. Inputs to this
 strict step are actual release stencils from the preceding step (or birth)
 in price-tagged order. No need to assume they transport in some ideal
 scheme. Other possible Laurent regulators welcomed as below.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Weft
open Filter Function Lattice RG Pressure Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Mask Matter Coat Frond
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side}
open Fan Brush Foramen Pastel
variable {v z r C w s t y η γ B a ε α κ K: ℝ} {j n m k N M : ℕ}
open Weft AnalyticBridge.VerifiedReset FrameBox Tensor
local notation "E"=> Directions G c
namespace Scene
variable {o: Site c} (X:Grove o) (FF: Config G c→ℝ)(i l K:ℕ)
variable (p:BudgetPoint) {K1:ℝ}
lemma tracks (k:ℕ) (b κ:ℝ) (P:Cabana.Pkt (Directions G c) (i+1)) (he:∀ u:Fin (i+1), ‖(b^u.val/b^(grain k)) • P u‖ ≤ C): Scene X κ l (grain k+i+1) (i+1) (fun s=>Scene.branch X s l (grain k) b κ P) C:= by
   let G0:=G; let n':=grain k; let Z(j: Fin (i+1)):= (b^j.val/b^n') • P j
   let g(s:ℝ) : Cabana.Pkt (Directions G c) (i+1):= s^n' • (fun j=> (s^j.val)⁻¹ • Z j)
   have hx s: Scene.branch X s l (grain k) b κ P= FrameBox.realise X l κ (g s):=by funext u; unfold FrameBox.realise g Scene.branch; rw [Cabana.actual_smul]; unfold Z; simp_rw [smul_smul]; rfl
   simp_rw [hx]; have hc:0≤C:= (norm_nonneg _).trans (he 0); refine ⟨hc,?_,fun s hs=>⟨_,rfl,fun j=>?_⟩⟩
   · refine Hex.invert fun x=> ?_; unfold realise Cabana.actual; simp_rw [Finset.sum_apply]; refine Hex.total Finset.univ fun j _=> ?_; let n:= grain k+i+1; let t:= n+n'-j.val; have hp:j.val≤n:=by unfold n; omega
     refine (Hex.held (k:=n) ⟨t,by unfold t n n'; omega⟩ (Tensor.diagonal (Z j) (X.crook l Chi.canonical κ x))).change fun s hs=>?_
     dsimp only; unfold mark Tensor.diagonal
     unfold g; rw [Pi.smul_apply,smul_smul]; rw [_root_.smul_apply, show s^t/s^n=s^n'*(s^j.val)⁻¹ from ?_]; swap; · rw [← div_eq_mul_inv,div_eq_div_iff (pow_ne_zero _ hs.1.ne') (pow_ne_zero _ hs.1.ne'),← pow_add,← pow_add]; congr 1; unfold t; omega
     rfl
   have h_:0 < s:=hs.1
   unfold g; rw [Pi.smul_apply,smul_comm (s^j.val),smul_inv_smul₀ (pow_ne_zero _ h_.ne'),norm_smul,Real.norm_of_nonneg (pow_nonneg h_.le _)]; exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ h_.le hs.2)).trans (he j)
-- canonical emitter for analytic inlet at true densities. Index `tag`; when tag too late mark omitted.Property exposed. Lambda.Summarize only scalar payment.We can also grant all Γ variants first.
lemma recovered (b:ℝ)(hz:b∈Weft.clip)(P: Cabana.Pkt (Directions G c) n)(z:ℕ)(κ:ℝ): Scene.branch X b l z b κ (FrameBox.clear X l P)= FrameBox.realise X l κ P:=by
    funext i; let F:= FrameBox.clear X l P; let f:Cabana.Pkt (Directions G c) n:=fun j=> ((b^j.val)⁻¹*(b^j.val/b^z)) • F j
    unfold Scene.branch; change b^z * Cabana.actual f (X.crook l Chi.canonical κ i)=_; have hp: f=(b^z)⁻¹ • F:=by
        funext j; unfold f; rw [← mul_div_assoc,inv_mul_cancel₀ (pow_ne_zero _ hz.1.ne'),one_div]; rfl
    rw [hp,Cabana.actual_smul,Pi.smul_apply,smul_eq_mul,mul_inv_cancel_left₀ (pow_ne_zero _ hz.1.ne')]; unfold F; rw [FrameBox.rays]; unfold Grove.crook; rw [Grove.range_id]; rfl
structure Opens {S':Side} (S: Rep G S') (r:ℕ→ℕ)(z p k:ℕ)(κ c : ℝ)(f:ℕ→ℝ→Pot G S'): Prop where
    calls : ∃ g:ℕ→ℝ, (∀ u,SumBudget (fun i=> if (S.activities.reg i).site=u then g i else 0) 1) ∧∀ i:ℕ,r i≤ p → CanX κ z k (pie p+1) (f i) (S.activities.reg i).site (g i*c)
    matchesAt (i:ℕ) : r i≤ p → S.activities.E i=f i (gStep S.beta)
structure Etched {S':Side} (S:Rep G S')(r:ℕ→ℕ)(z k:ℕ)(κ:ℝ)(F:ℕ→ℝ→ Config G S'→ℝ) : Prop where
    powers (i:ℕ) : r i ≤ k →let b:= S.activities.reg i; ∃ (m:ℕ)(V:Grove b.site)(U: Cabana.Pkt (Directions G S') (pie (r i)+1)), m≤z ∧ S.activities.E i=FrameBox.realise V m κ U∧ F i=(fun s=> Scene.branch V s m (grain (r i)) (gStep S.beta) κ (FrameBox.clear V m U))
lemma readings (G:Gauge)(j:ℕ)(L:Side)(κ:ℝ)(hp:Reliable G κ v)(K:ℕ)(hK:trackPower j ≤ K) : ∃ M:ℝ→ℝ, Rate G L 0 M∧ ∀ᶠ t in atTop, let x:=betaF G t L; 0≤ M t∧∀ (c:Side) (b:Rep G c)(v:ℕ→ℕ)(z z':ℕ), b.beta ∈ Set.Icc (x/2) (2*x)→b.p.threshold=Pressure.fiery G t L→ PhysicalNext.Repeat.Coup.License j b κ x v z → z≤ z' → ∃ U:ℕ→ℝ→ Config G c→ℝ,Opens b v z' j K κ (M t) U ∧ Scene.Etched b v z' j κ U:=by
    choose f H h using fun i:Fin (j+1)=> harvestT G (pie i.val) hp L i.val
    let M x:=∑ i,|f i x|
    refine ⟨M,fuelReel _ H _,?_⟩
    filter_upwards [(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1, eventually_all.mpr h, (PhysicalNext.Repeat.Sienna.glim G L).below (by norm_num) 1 zero_lt_one] with t hZ he hp' x
    refine ⟨sum_nonneg (fun i _=>abs_nonneg _),fun c b v z z' hV hP hL hz=>?_⟩
    obtain ⟨g,hG,hK',h⟩:= PhysicalNext.Repeat.Coup.comply hL hZ z' hz
    let a:= gStep b.beta; have ha : a∈Weft.clip:= by obtain ⟨h,hg⟩ := PhysicalNext.Repeat.Sienna.lamp G L (zero_lt_one.trans_le hZ) b.beta hV.1; exact ⟨h,hg.trans ((le_abs_self _).trans hp')⟩
    choose F HF using fun i:ℕ=> show ∃ f:ℝ→ Config G c→ℝ, v i ≤ j → ∃ M₁:ℕ, M₁≤z'∧∃ (G':Grove (b.activities.reg i).site)(P:Cabana.Pkt (Directions G c) (pie (v i)+1)), b.activities.E i = FrameBox.realise G' M₁ κ P∧ f=(fun s=> Scene.branch G' s M₁ (grain (v i)) a κ (FrameBox.clear G' M₁ P))∧ CanX κ z' K (pie j+1) f (b.activities.reg i).site (g i*M t) from by -- edit
              by_cases hy:v i ≤ j; swap; · refine ⟨fun _=> (0:Config G c→ℝ),fun h=> (hy h).elim⟩
              obtain ⟨⟨V,ht,G',P,hp⟩,hh⟩:=hK' i hy
              rw [hp] at hh; let X':=FrameBox.clear G' V P; let t':Fin (j+1):= ⟨v i,by omega⟩
              let U(s:ℝ):= Scene.branch G' s V (grain (v i)) a κ X'
              have Hg:0≤g i:= by simpa using (hG (b.activities.reg i).site).1 i
              have hu:= he t'|>.2 c b.beta hV.1 hV.2 b.p V hP _ G' P _ (b.activities.reg i|>.support) Hg hh
              have hx:0≤f t' t:=(he _|>.1)
              have hs: f t' t ≤ M t:= (le_abs_self _).trans (Finset.single_le_sum (f:=fun i=> |f i t|) (fun i _=>abs_nonneg _) (Finset.mem_univ t'))
              have hC: Scene G' κ V K (pie j +1) U (g i * M t):=by
                   refine (((tracks G' (pie (v i)) V (v i) a κ X' hu).generous _ ((Scene.powers j (v i) hy).trans hK) (mul_le_mul_of_nonneg_left hs Hg)).padding ?_); unfold pie; omega
              exact ⟨U,fun _=>⟨V,ht,G',P,hp,rfl,⟨V,ht,G',hC⟩⟩⟩
    refine ⟨F,⟨⟨g,hG,fun i hi=> by obtain ⟨V,hv,G',P,he,H⟩:= HF i hi; exact H.2⟩,fun i hi=>?_⟩,⟨fun i hi=>?_⟩⟩
    · obtain ⟨V,hv,G',P,he,hF,hC⟩:= HF i hi; rw [he,hF]; exact (recovered _ V a ha P _ _).symm
    obtain ⟨V,hv,G',P,he,hF,hC⟩:= HF i hi; exact ⟨V,G',P,hv,he,hF⟩
end Scene
end YM.LocalLTE.Weft
