import YM.LocalLTE.FieldPT.Coin
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
variable {o: Site c} (X:Grove o) (f: Config G c→ℝ)(i l K:ℕ)
-- local convention so `X.normEvidence` normalized powers.La.Does NOT depend on future.Compares to any scene forecast and pays exponent. Particular witness uses symmetry-saturated frames.
def grain (m:ℕ) : ℕ:= Nat.floor (-2*(Pastel.chip m + Pastel.slack))
lemma grained (m:ℕ) : (1/2:ℝ)*grain m ≤ -(Pastel.chip m+Pastel.slack)∧2 ≤ grain m:=by
    have hz: (2:ℝ) ≤ -2*(Pastel.chip m+Pastel.slack):=by unfold Pastel.chip Pastel.slack; linarith only [Nat.cast_nonneg (α:=ℝ) m]
    exact ⟨(by linarith only [show (grain m:ℝ) ≤ _ from Nat.floor_le (a:=-2*(Pastel.chip m+Pastel.slack)) (by linarith)]),Nat.le_floor (by exact_mod_cast hz)⟩
abbrev trackPower (p:ℕ) := p+100+Scene.grain p
lemma powers (j:ℕ)(h:j≤ i) : grain j+pie j+1 ≤ trackPower i:=by
   unfold trackPower; have ht: grain j ≤ grain i:=Nat.floor_le_floor (by unfold Pastel.chip; linarith only [Nat.cast_le (α:=ℝ)|>.mpr h]); unfold pie; omega
noncomputable def branch (s:ℝ) (l:ℕ) (i:ℕ)(g:ℝ)(κ:ℝ)(Q:Cabana.Pkt E n):Pot G c:=s^i • FrameBox.realise X l κ (fun j=>((s^j.val)⁻¹*(g^j.val / g^i)) • Q j)
section
variable (K:ℕ)
lemma fuelReel {ι:Type*}(g:ι→ℝ→ℝ)(he:∀ i:ι, Rate G L 0 (g i))(S:Finset ι): Rate G L 0 (fun x=>∑ i∈S,|g i x|):=by
    induction S using Finset.induction_on with
    | empty=> exact Rate.const 0
    | insert i I h ih=> simp_rw [Finset.sum_insert h]; exact ((he i).compare (v:=fun x=> |g i x|) (Eventually.of_forall fun t=> (abs_abs _).le)).add ih
lemma harvestT (G:Gauge)(d:ℕ){κ k:ℝ}(hp:Reliable G κ k)(L:Side)(q:ℕ): ∃ M:ℝ→ℝ, Rate G L 0 M∧∀ᶠ x in atTop,0≤ M x∧∀ c:Side,∀ s:ℝ, betaF G x L/2 ≤ s→ s≤2*betaF G x L → ∀ (p:BudgetPoint)(m:ℕ),p.threshold=Pressure.fiery G x L →∀ (o:Site c)(X:Grove o)(P:Cabana.Pkt (Directions G c) (d+1))(ξ:ℝ)(v:Support c), 0 ≤ ξ→p.supBounds o v (FrameBox.realise X m κ P) (ξ*(betaF G x L) ^(chip q+slack)) →let g:= gStep s
      ∀ i:Fin (d+1), ‖(g^i.val/g^(grain q)) • FrameBox.clear X m P i‖ ≤ ξ*M x :=by -- via Cabana.price
    obtain ⟨U,hU,hA⟩:= Grove.sound_ball G (χ:=Chi.canonical) hp
    choose C hC hV using fun i:Fin (d+1)=> Cabana.price (d+1) i
    let g(x:ℝ):=2*gStep (betaF G x L); let f(x:ℝ):=Real.sqrt (2*betaF G x L)
    let w:=chip q+slack
    let u(x:ℝ):= (U*Pressure.fiery G x L)⁻¹; let M(i:Fin (d+1)) (x:ℝ):= g x^i.val*(f x^(grain q)) *(C i * ((betaF G x L)^w) * (u x)^i.val)
    have hh: Rate G L (1/2) f:= by
       apply (Rate.mul_left (Rate.power (G:=G) (L:=L) (a:=1/2)) (Real.sqrt 2)).compare; filter_upwards with i; exact le_of_eq (congr_arg abs (Real.sqrt_mul (by norm_num) _ |>.trans (by rw [Real.sqrt_eq_rpow (betaF ..)])))
    have hv:Rate G L (1/2) u:= by unfold u; simpa only [_root_.mul_inv_rev] using! ((inverse_mist G L).mul_right U⁻¹)
    have he (i):Rate G L 0 (M i):= ((((PhysicalNext.Repeat.Sienna.glim G L).pow i.val).mul (hh.pow (grain q))).mul (((Rate.power (G:=G) (L:=L) (a:=w)).mul_left (C i)).mul (hv.pow i.val))).weaken (by unfold w; linarith only [(grained q).1])
    let Z x:= ∑ i,|M i x|
    refine ⟨Z, fuelReel M he univ,?_⟩
    filter_upwards [Delay.shift_pos G L] with x hx
    refine ⟨Finset.sum_nonneg fun _ _=> abs_nonneg _,fun c t ht hp p m hh o X P ξ v hz hr i=>?_⟩; let b:=gStep t
    let F:=FrameBox.clear X m P; let s:= U*Pressure.fiery G x L; have hs:0<s:=mul_pos hU (hh ▸ p.threshold_pos); have hθ:= hA c p o X m
    have hP: ‖F i‖ ≤ C i * (ξ *betaF G x L ^w)* s⁻¹^i.val:= hV _ _ _ _ _ (FrameBox.cleans _ _ _) hs hr.1 fun y hy=> (?_) -- edit
    swap
    · obtain ⟨he,hZ⟩:= hθ y (show ‖y‖≤U*p.threshold from hh.symm ▸ hy)
      have hk:= hr.2 _ (hZ.mono_left (Finset.subset_univ v)) [] (by simp) (by simp); change ‖Cabana.actual P _‖ ≤ _ at hk; rw [show FrameBox.Grove.crook X m Chi.canonical κ _= X.shore m y from he] at hk; exact (le_of_eq (congr_arg _ (FrameBox.rays ..))).trans hk
    have hb:=PhysicalNext.Repeat.Sienna.lamp G L hx t ht; have hu: b⁻¹ ≤ f x:=by unfold b gStep f; rw [inv_inv]; exact Real.sqrt_le_sqrt hp
    rw [div_eq_mul_inv,← inv_pow,norm_smul,Real.norm_of_nonneg (mul_nonneg (pow_nonneg hb.1.le _) (pow_nonneg (inv_nonneg.mpr hb.1.le) _))] -- edit div
    apply (mul_le_mul (mul_le_mul (pow_le_pow_left₀ hb.1.le hb.2 i.val) (pow_le_pow_left₀ (inv_nonneg.mpr hb.1.le) hu (grain q)) (pow_nonneg (inv_nonneg.mpr hb.1.le) _) (pow_nonneg (hb.1.le.trans hb.2) _)) hP (norm_nonneg _) (mul_nonneg (pow_nonneg (hb.1.le.trans hb.2) i.val) (by unfold f; positivity))).trans
    have ht:= (mul_le_mul_of_nonneg_left (single_le_sum (f:=fun i=> |M i x|) (fun _ _=>abs_nonneg _) (Finset.mem_univ i)) hz); apply le_trans _ ht
    refine (le_of_eq (by unfold M; dsimp only [u,s]; ring : _= ξ*M i x)).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hz)
end
end Scene
end YM.LocalLTE.Weft
