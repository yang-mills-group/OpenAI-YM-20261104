import YM.AllOrder.Catch.Tune
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Catch
open Function Set Filter Matrix Metric MeasureTheory ProbabilityTheory Finset
open ConnectedActivityE6 Blaze Brush Poll Local Vote Clock
open PositionX.Jet PhysicalNext Repeat Lantern
open scoped Topology ENNReal BigOperators Classical ContDiff Polynomial
variable {X:Type*}{S:Clock X}{f g:X→ℝ}{a b C:ℝ}{V:X→Type}{j k:ℕ}
variable [∀ i,Fintype (V i)][∀ i,DecidableEq (V i)]
variable (M:∀ i, Matrix (V i) (V i) ℝ) (D : X→ℝ) {N Z : X→ℝ}
local notation "Y"=> (fun i=> Body (V i))
local notation "L"=> Sigma (Y)
local notation "Ξ"=> (fun i=> Metric.closedBall (0:Y i) (D i))
local notation "μ"=> fun i=> sweep (M i)
structure Gate (S:Clock X)(M:∀ i, Matrix (V i) (V i) ℝ)(D:X→ℝ): Prop where
   sizes : S.Meter (fun i=>(Fintype.card (V i):ℝ)) 0
   gram : ∃ c,∀ᶠ i in S.rail,(M i).PosDef ∧ ∀ z:V i→ℝ, dotProduct z ((M i) *ᵥ z) ≤ c*dotProduct z z
   width : S.Meter D 0
   mass b : S.Meter (fun i=> (sweep (M i)).real (Metric.closedBall (0:Body (V i)) (D i))ᶜ) b
local notation "Q"=> S.stage (Y)
local notation "Pt"=> Clock.tier (Y) S
local notation "P"=> S.book (Ξ)
namespace Gate
variable {M D}
lemma paint_G (h:Gate S M D){K:Type*}{Q':Clock K}(p:K→X)(he:S.Fare (U:=Q') p): Gate Q' (V:=fun i=> V (p i)) (fun i=> M (p i)) (D∘ p):=by -- change Y' syntax generic map
 obtain ⟨hs,⟨C,hC⟩,h,hf⟩:=h; exact ⟨hs.pays _ he, ⟨C,he.tends.eventually hC⟩,h.pays _ he, fun v=> (hf v).pays _ he⟩
lemma volumes (S:Clock X)(h:S.Meter f 0)(j:ℕ)(c:ℝ):S.Meter (fun i=> volumeCost c j (f i)) 0:= by unfold volumeCost; exact (((Meter.const S 1|>.add h).pow j).unitPay (by simp) ((Meter.const _ _).add (h.rscale _)))
section first
variable {E:∀i, Body (V i)→ℝ}(h:Gate S M D)(he:(Clock.tier (fun i=> Body (V i)) S).Quite (fun i=> E i.1 i.2))(hx:∀ᶠ i in S.rail, AEStronglyMeasurable (E i) (sweep (M i)))
include h hx he
lemma healthy : ∀ᶠ i in S.rail, Integrable (E i) (μ i):= by
 obtain ⟨n,hp⟩:= Quite.tier_bound (Z:=fun i=> Body (V i)) (S:=S) (fun i=> E i.1 i.2) he; obtain ⟨c,hc⟩:=h.gram; filter_upwards [S.pos,hp,hc,hx] with i hi hI hv ht; exact average hv.1 hv.2 ht le_rfl hI|>.1
lemma creep (b:ℝ) : S.Meter (fun i=> ∫ z in (Ξ i)ᶜ,E i z ∂(μ i)) b:= by
 obtain ⟨n,hp⟩:= Quite.tier_bound (Z:=fun i=> Body (V i)) (S:=S) (fun i=> E i.1 i.2) he; obtain ⟨c,hc⟩:=h.gram; let s:ℝ:=b-n; let v := h.mass (s+s); let N x:= S.cost x^(n:ℕ); let n₀:= 2*n; let V₀ x:= volumeCost c n₀ (Fintype.card (V x)); let g:S.Meter N n:= by simpa only [Real.rpow_natCast] using Meter.pale S n
 let t x:= S.cost x^(-s); let p x:= (sweep (M x)).real (Ξ x)ᶜ; have ht:S.Meter (fun i=> (t i)⁻¹) s:= (Meter.pale S s).eq_mem (S.positive.mono fun i hi=> by unfold t; dsimp only; rw [Real.rpow_neg hi.le,inv_inv]);
 have hh : S.Meter (fun i=> N i*(t i*p i+ V₀ i * (t i)⁻¹)) b:= (g.mul ((((Meter.pale S (-s)).mul v).weak (by linarith : -s+(s+s) ≤ s)).add ((volumes S h.sizes _ _).unitPay le_rfl ht))).weak (by unfold s; linarith)
 apply hh.smaller; filter_upwards [S.positive,hx,hp,hc] with i hi hp hv hs; rw [← integral_indicator measurableSet_closedBall.compl]; apply (lift_tail hs.1 hs.2 hp le_rfl hv _ (t i) (Real.rpow_pos_of_pos hi _)).trans; rw [div_eq_mul_inv]; exact le_abs_self _
omit he hx in
lemma closeness (hp:∀ᶠ i in S.rail,IntegrableOn (E i) (Metric.closedBall (0:Body (V i)) (D i)) (sweep (M i)))(hg:(P).Meter (fun i=>E i.1 i.2.1) b): S.Meter (fun i=>∫ z in Ξ i,E i z ∂(μ i)) b:= by
 intro v hv; have hs:= S.booked (Ξ) (fun i j=> |E i j|≤ S.cost i^v)|>.1 (show ∀ᶠ i in (P).rail, |E i.1 i.2.1|≤ S.cost i.1^v from hg v hv);
 filter_upwards [hs,S.positive,hp] with i hi hI hp; let E':= E i; let N':=(μ i).restrict (Ξ i); let F:= S.cost i^v
 have ht := (norm_integral_le_integral_norm («μ» := N') E').trans (integral_mono_ae hp.norm (g:=fun v=> F) (integrable_const _) ((ae_restrict_mem measurableSet_closedBall).mono fun j (hj:j∈Ξ i)=> (show ‖E' j‖≤ F from hi j hj))); rw [integral_const,show N'.real Set.univ=_ from measureReal_restrict_apply_univ («μ» := sweep (M i)) (Ξ i)] at ht; exact ht.trans (mul_le_of_le_one_left (Real.rpow_pos_of_pos hI _).le (measureReal_le_one)) -- lemma name
lemma total (hp:(P).Meter (fun i=> E i.1 i.2.1) b): S.Meter (fun i=> ∫ z,E i z ∂(μ i)) b:= by
 let D:= healthy h he hx; exact Clock.Meter.eq_mem ((closeness (h:=h) (D.mono fun _ hi=> hi.integrableOn) hp).add (creep h he hx _)) (D.mono fun i hi=> integral_add_compl measurableSet_closedBall hi)
-- mixes all. inside integrable ∧ coeff. Local requires high_order tilt projection.
end first
variable {E:∀ i,Body (V i)→ℝ}
variable (E M D) (U:X→ℝ) (C:∀ i:X,Body (V i)→Word ℝ)
local notation "A"=> fun i n=>∫ z,C i z n ∂(μ i)
variable (h: Gate S M D)(hl:TaylorCap (S.book (fun i=> Metric.closedBall (0:Body (V i)) (D i))) k (U∘Sigma.fst) (fun i=> E i.1 i.2.1) (fun i=>C i.1 i.2.1))(hv: S.Quite U)
abbrev OnAct (u:∀ i, Body (V i)→ℝ):=∀ᶠ i in S.rail,AEStronglyMeasurable (u i) (sweep (M i))
variable (hT:∀ᶠ i in S.rail,IntegrableOn (E i) (Metric.closedBall (0:Body (V i)) (D i)) (sweep (M i)))(hc:∀ j≤k,(Clock.tier (fun i=> Body (V i)) S).Quite (fun v=> C v.1 v.2 j))
    (ht: ∀ j≤k, OnAct (S:=S) M (fun i z=> C i z j))
include h hv hl hT hc ht
lemma part : TaylorCap S k U (fun i=> ∫ z in (Ξ i),E i z ∂(μ i)) (A):= by
 have hp j (hj:j≤k) := healthy h (hc j hj) (ht _ hj); let Y₀ i:= (μ i).restrict (Ξ i); let Y₁ i:= (μ i).restrict (Ξ i)ᶜ; refine ⟨fun j hj=>?_ , fun j hj=>?_⟩
 · exact total (E:=fun i z=>C i z j) h (hc j hj) (ht _ hj) (hl.steps j hj)
 let E' i (x:Body (V i)):= delay (C i x) j (U i); let θ i:= ∫ x,E' i x ∂ (Y₀ i); let π i:= delay (A i) j (U i)
 let htL (i:X)(v:ℕ):=∫ x,C i x v ∂ (Y₁ i); let u:= graded (j+1); let ℓ:= range (j+1); let f' (x:ℕ)i:= U i ^ x * htL i x;
 let H₀:= eventually_all.mpr (show ∀ u:Fin (k+1),∀ᶠ i in S.rail, Integrable (fun z=> C i z u.val) (μ i) from fun u=> hp u.val (by have h':=u.isLt; omega));
 have hμ : ∀ᶠ i in S.rail, Integrable (E' i) (Y₀ i) ∧ θ i + (∑ w∈ℓ, f' w i) = π i := by
    filter_upwards [H₀] with i hi; have hv (w:ℕ)(hw:w∈ℓ):= hi ⟨w,(by unfold ℓ at hw; rw [Finset.mem_range] at hw; omega)⟩; have hr (w:ℕ) hw:= ((hv w hw).const_mul (U i^w)) ; have hh (w:ℕ) hw:= (hv w hw).const_mul (U i ^ w)|>.integrableOn (s:=Ξ i)
    refine ⟨MeasureTheory.integrable_finsetSum ℓ (fun j hj=> hh j hj),?_⟩
    unfold θ E' π delay; rw [integral_finsetSum]; swap; · exact fun j hj=> hh j hj
    rw [←sum_add_distrib]; apply Finset.sum_congr rfl; intro w hw; simp_rw [smul_eq_mul]; unfold f' htL; rw [integral_const_mul,← mul_add,show _+_=_ from integral_add_compl measurableSet_closedBall (hv w hw)]
 have hA:= hl.stamps j hj; let Z₀ i:= ∫ z,E i z ∂(Y₀ i); have hπ : S.Meter (fun i=>Z₀ i-θ i) u:= by
    apply Clock.Meter.eq_mem (closeness (h:=h) (S:=S) (E:=fun i=>E i-E' i) ( (hμ.and hT).mono fun i hi=> Integrable.sub hi.2 hi.1.1) hA); exact (hμ.and hT).mono fun i hi=> integral_sub' hi.2 hi.1.1
 obtain ⟨p,hp⟩:=hv
 have hL:S.Meter (fun i=>∑ j∈ℓ,f' j i) u:= by apply Clock.Meter.sum; intro j' hj'; have hx:j'≤k:=(by have hh:=Finset.mem_range.mp hj'; omega); exact (((hp.pow j').mul (creep h (hc j' hx) (ht j' hx) (u-p*j'))).weak (by linarith)) -- shadow ht
 exact Clock.Meter.eq_mem (hπ.sub hL) (hμ.mono fun i hi=> (show Z₀ i-θ i-_ = Z₀ i-π i from (by rw [← hi.2]; ring)))
end Gate
end YM.AllOrder.Catch
