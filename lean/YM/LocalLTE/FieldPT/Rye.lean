import YM.LocalLTE.FieldPT.Survey
/-!
 Laurent basis load behind an aligned support. Basis terms are independent predictor
 coefficients, not the response. Record letters $T_{a,d}$ basis from input frame.X.
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
variable {o: Site c} (X:Grove o) (f:ℝ→ Config G c→ℝ)(i l:ℕ)
def tallyF (s:ℝ) := Tensor.coeff (f s ∘ Grove.soloV ∘ X.shore l) i 0
lemma symCost (C : Tensor.T E ℝ i) (s:ℝ) : ‖s • Tensor.symmetrize C‖≤ ‖s • C‖:=by
    unfold Tensor.symmetrize; rw [smul_comm,Finset.smul_sum,norm_smul,norm_smul];
    let n:= Fintype.card (Equiv.Perm (Fin i)); have he:0<(n:ℝ):=by unfold n; positivity
    rw [norm_inv,Real.norm_of_nonneg he.le,inv_mul_eq_div]; apply (div_le_iff₀ he).mpr
    apply le_trans (norm_sum_le ..); simp_rw [norm_smul]; have hz (s:Equiv.Perm (Fin i)): ‖C.domDomCongr s‖=‖C‖:=by
       exact ContinuousMultilinearMap.norm_domDomCongr .. -- edit
    simp_rw [hz]; rw [Finset.sum_const,nsmul_eq_mul,card_univ]; unfold n; apply le_of_eq; ring -- edit
lemma standing {P:Cabana.Pkt (Directions G c) n}(i:Fin n)(hp:Reliable G κ K) (w:BudgetPoint) (hr:f s=realise X l κ P):
   tallyF X f i.val l s=FrameBox.clear X l P i:= by
    obtain ⟨U,hU,H⟩:= Grove.sound_ball G (χ:=Chi.canonical) hp
    have he: (f s ∘ Grove.soloV ∘ X.shore l) =ᶠ[𝓝 0] Cabana.actual (FrameBox.clear X l P):= by
       filter_upwards [Metric.ball_mem_nhds (0:E) (mul_pos hU w.threshold_pos)] with v hv
       have hh:= H c w o X l v (mem_ball_zero_iff.mp hv).le|>.1
       simp only [hr,Function.comp_apply, realise, hh, FrameBox.rays]
    exact (Tensor.GermCoeff i.val he).trans (Cabana.reading _ (FrameBox.cleans X l P) i)
lemma strengthX (u:ℝ)(p:Cabana.Pkt (Directions G c) n)(i:Fin n): ‖u • FrameBox.clear X l p i‖ ≤ ‖u • p i‖:=by
    unfold FrameBox.clear
    refine (symCost _ _ _).trans (?_); rw [norm_smul,norm_smul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans; apply mul_le_of_le_one_right (norm_nonneg _); simp only [prod_const,card_univ,Fintype.card_fin]; apply pow_le_one₀ (norm_nonneg _); refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x=>?_ ; rw [one_mul]; exact Grove.norm_shore ..
noncomputable def kernelF (L:J k) := pick k (tallyF X f i l) L
lemma invested (w:BudgetPoint)(p:Scene X κ l k n f C) (hp:Reliable G κ K) (he:i<n): Hex k (Scene.tallyF X f i l) ∧ ∀ s∈clip, ‖s^i • Scene.tallyF X f i l s‖ ≤ C:=by
   have ht s (hs:s∈clip): ContDiffAt ℝ (↑i) (f s ∘ Grove.soloV ∘ X.shore l) 0:= by
      obtain ⟨P,hP,_⟩:=p.plaque s hs; rw [hP,show Grove.soloV=increment (1:Config G c) from Hall.bare.symm]; exact (show ContDiffAt ℝ _ (realise X l κ P ∘ increment 1) (X.shore l 0) from (by rw [map_zero]; exact (Cabana.moves _ _).contDiffAt.comp 0 (Hall.clip_ok _ X hp _ _))).comp _ (X.shore l).contDiff.contDiffAt
   refine ⟨Hex.smoothWork (Hex.invert (f:=fun s=>f s ∘ Grove.soloV ∘ X.shore l) fun i=>p.weft.use _) ht, fun s hs=> ?_⟩; obtain ⟨P,hP,hF⟩:= p.plaque s hs; rw [standing X f _ ⟨i,he⟩ hp w hP]; exact (strengthX X l _ _ _).trans (hF _)
lemma subPrice (w:BudgetPoint)(p:Scene X κ l k n f C)(hp:Reliable G κ K)(he:i<n)(u:J k):
   ‖Scene.kernelF X f i l u‖≤ (∑ j:J k,|slate k j u|/(probe k j)^i)*C ∧ (u.val+i<k → Scene.kernelF X f i l u=0):=by
    obtain ⟨hF,hK⟩:=Scene.invested X f i l w p hp he
    exact ⟨caisson u hK,Weft.vanish hF hK u⟩ -- edit
-- canonical caps Read.Check agree.Main uses *Color coefficient projection after tally*
attribute [local instance] Gauge.frobInner
lemma recordOne (w:BudgetPoint)(h:Scene X κ l k n f C)(hp:Reliable G κ K)(s:ℝ)(he:s∈clip): f s= FrameBox.realise X l κ (fun i:Fin n=> tallyF X f i.val l s):= by
   obtain ⟨P,hP,hΞ⟩:= h.plaque _ he
   rw [show (fun i:Fin n=> tallyF X f i.val l s)=FrameBox.clear X l P from funext (fun i=> standing X f l i hp w hP),hP]; funext u; unfold FrameBox.realise; rw [FrameBox.rays]; unfold Grove.crook; rw [X.range_id]
-- clover color projector chosen separately, commutes Psi/G.
lemma invariance {X':Support c}(p:BudgetPoint)(h:p.Regular X' (f s))(Q:Cabana.Pkt (Directions G c) n)(hp:Reliable G κ K) (he:f s=realise X l κ Q): f s=realise X l κ (colorP Q):=by
    funext t; rw [realise, FrameBox.sunwheel]; let z:=X.crook l Chi.canonical κ t
    have he' i:Cabana.actual Q (wheel i z)= f s t:= by
        let g:=fun _ : Site c=>i; have hv:= FrameBox.wheel_away X hp g l t; rw [← (show _=wheel i z from hv)]; exact (congr_fun he (gauge g t)).symm.trans (h.symmetry g t)
    change _=∫ i:G.El,Cabana.actual Q (wheel i z) ∂G.probHaar; simp_rw [he']; simp
end Scene
end YM.LocalLTE.Weft
