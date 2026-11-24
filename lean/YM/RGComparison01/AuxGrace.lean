import YM.RGComparison01.AuxConstant

/-! # Use *full* cover coefficients on the constructed primary chart

Vote removes the quadratic saddle with its actual moving Hessian (see Lantern).
Cut-ball C^k and size estimates don't apply on the formal jet integral's domain.
Prove polynomial-growth separately, still with all order/volume costs visible.
No complex continuation of masks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.AuxGrace
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Lattice Wilson RG Pressure Push.AbsoluteSums PhysicalNext.Repeat Lantern
open ConnectedActivityE6 Blaze Brush Poll Shield WithLp Matrix Work.G05 AuxConstant
open scoped Topology MatrixOrder ContDiff BigOperators Classical Interval ENNReal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local notation "Y" => Poll.Body ι
variable {ϕ ψ : E × Poll.Body ι → ℝ} {ρ : E → Poll.Body ι} {M : E → Matrix ι ι ℝ}
    {p u v D a r w c : ℝ} {j k : ℕ}
variable (h : Golf ϕ ψ ρ M j D u v p)
local notation "S" => sweep (M 0)⁻¹

include h
lemma shrink (hr : 0≤r) (hh : r ≤ D) (he : 0 < w) (hw : w ≤ u) (ha : 0 < a) (hx : a ≤ v) (hi : k ≤ j) : Golf ϕ ψ ρ M k r w a p:= by
  refine ⟨he,ha,hw.trans h.small,hx.trans h.small',hr, fun x hi'=> (h.curve x (hi'.trans_le hw)).smaller (by omega), ?_,fun x hi=> h.station x (hi.trans_le hw),fun x hi'=> ⟨(h.gram x (hi'.trans_le hw)).1, ((h.gram x (hi'.trans_le hw)).2).smaller hi⟩⟩
  intro z t x hu he hv hi'; obtain ⟨h₁,h₂⟩ := h.color z t x (hu.trans hh) he (hv.trans_le hx) (hi'.trans_le hw)
  exact ⟨h₁.smaller (by omega),h₂.smaller hi⟩
lemma rolls (ha : 1 ≤ a) : Golf ϕ ψ ρ M j (D*a) u (v/a) p:= by
  have hp : 0<a:=zero_lt_one.trans_le ha
  refine ⟨h.pos,div_pos h.pos' hp,h.small, (div_le_self h.pos'.le ha).trans h.small',mul_nonneg h.off hp.le,h.curve,?_,h.station,h.gram⟩
  rintro z t ⟨b,x⟩ hz ht he hw
  let z' := a⁻¹ • z
  have h' : ‖z'‖ ≤ D := by
    unfold z'; rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hp).le,← div_eq_inv_mul]; exact (div_le_iff₀ hp).mpr hz
  have hx : ‖b*a‖ < v:= by rw [norm_mul,Real.norm_of_nonneg hp.le]; exact (lt_div_iff₀ hp).mp he
  rw [show visit ρ z t (b,x) = visit ρ z' t (b*a,x) from (by simp [visit,z',smul_smul,hp.ne'])]; exact h.color z' t (b*a,x) h' ht hx hw

omit h
lemma scale_clump {w u u' b : ℝ} (k : ℕ) (_hu : 0≤u) (he : 0 ≤ u') (hb : 0 ≤ b) (hr : 1 ≤ w) (h : u' ≤ u*w) : clump k u' b ≤ clump k u b * w^k := by
  unfold clump;  rw [mul_assoc (k.factorial * b) _ (w^k),← mul_pow]
  simp only [mul_one]; gcongr; nlinarith

def zgrade (j : ℕ) := (j+2)*j
lemma grow {D' : ℝ} (j : ℕ) (hD : 0 ≤ D) (h : D' = D*a) (hA : 1 ≤ a) (hp : 0≤p) : fee j p D' ≤ fee j p D * a^(j+2):= by
  subst D'; let f:=fee j p D; have he : 0 ≤ D*a:=by positivity
  have H : 0 ≤ spanE p (D*a):= by unfold spanE; positivity
  have hf : 0 ≤ spanE p D:= by unfold spanE; positivity
  have hv:= scale_clump j hf H hp hA (show spanE p (D*a) ≤ spanE p D*a by unfold spanE; nlinarith only [hA, hp,mul_le_mul_of_nonneg_left hA hp])
  have hg : acrossE j p (D*a) ≤ acrossE j p D * a^(j+2):= by
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv he) he).trans_eq ?_
    unfold acrossE; ring
  have hV : clump j (spanE p (D*a)) p ≤ clump j (spanE p D) p * a^(j+2):= hv.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA (by omega)) (by unfold clump; positivity))
  unfold fee; rw [add_mul, add_mul, add_mul (acrossE ..), add_mul (clump ..)]
  exact add_le_add (add_le_add (le_mul_of_one_le_right (add_nonneg hp hp) (one_le_pow₀ hA)) (add_le_add hg hg)) (add_le_add hV hV)

abbrev nodes (ϕ ψ : E×Poll.Body ι→ℝ) (ρ : E→Poll.Body ι) (M : E→Matrix ι ι ℝ) (z:Y) := Real.exp ∘ grace ϕ ψ ρ M z

include h
variable [FiniteDimensional ℝ E]
local notation "U" => nodes ϕ ψ ρ M
lemma buds (hv : 1≤ D) (he : Brush j c 1 Real.exp 0) (z:Y) : Brush j
    (clump j (fee j p D) c * (1+‖z‖)^zgrade j) 1 (nodes ϕ ψ ρ M z) 0:= by
  let a:=1+‖z‖; have ha:1 ≤ a:= le_add_of_nonneg_right (norm_nonneg z)
  have hD := rolls h ha; have hm : ‖z‖ ≤ D*a := (show ‖z‖ ≤ a from le_add_of_nonneg_left zero_le_one).trans (le_mul_of_one_le_left (by positivity) hv)
  have hz: ‖(0:E)‖ < u:=by rw [norm_zero]; exact h.pos
  have hp := (h.curve 0 hz).nonneg
  have hV : 0 ≤ fee j p D:= (compel D (x:=(0,0)) (z:=0) h hz (by rw [norm_zero]; exact h.pos') (by rw [norm_zero]; exact h.off)).nonneg
  have hw := compel _ hD (x:=(0,0)) hz (by change ‖(0:ℝ)‖ < _; rw [norm_zero]; exact hD.pos') hm
  have ht : Brush j (clump j (fee j p (D*a)) c) 1 (U z) 0:= composite hw (by rw [show grace ϕ ψ ρ M z 0 = _ from zeroC ϕ ψ ρ M z]; exact he)
  refine ht.climb ?_ le_rfl; unfold zgrade; rw [pow_mul]
  exact scale_clump j hV hw.nonneg he.nonneg (one_le_pow₀ ha) (grow j h.off rfl ha hp)

-- Only need these cutoffs with compact domain, no analytic or uniform
-- claims in D; genuine neighborhoods exclude bad points for every vote.
lemma neighbors (hr : 0≤r) (hh : 1≤D) : ∃ c : ℝ,0 ≤ c ∧ ∀ᶠ y in 𝓝 (0:ℝ×E),
    Measurable (truncate (nodes ϕ ψ ρ M) r y) ∧
    ∀ z:Y, Brush j c 1 (fun y=> truncate (nodes ϕ ψ ρ M) r y z) y:= by
  let a:=1+r; have ha:1 ≤ a:= le_add_of_nonneg_right hr
  have hR:= rolls h ha; have hb:= hR.pos'; have hD : r ≤ D*a:= (le_add_of_nonneg_left zero_le_one).trans (le_mul_of_one_le_left (by positivity) hh)
  have h:= shrink hR hr hD hR.pos le_rfl hb le_rfl (le_refl j)
  let F:= fee j p r
  have h' : ‖(0:E)‖<u:= by rw [norm_zero]; exact h.pos
  have hp' : ‖(0:ℝ)‖<v/a:=by rw [norm_zero]; exact hb
  have hF : 0 ≤ F:= (compel _ (x:=(0,0)) h h' hp' (z:=0) (by rw [norm_zero]; exact hr)).nonneg
  obtain ⟨d,hd,he⟩:= Brush.compact (f:=Real.exp) (k:=j) (s:=Icc (-F) F) isCompact_Icc (fun z _=> Real.contDiff_exp.contDiffAt)
  let C:= clump j F d; have hC : 0 ≤ C:=by unfold C clump; positivity
  refine ⟨C,hC,?_⟩; filter_upwards [(continuous_norm.comp continuous_snd|>.continuousAt (x:=((0,0):ℝ×E))|>.eventually (gt_mem_nhds h')), (continuous_norm.comp continuous_fst|>.continuousAt (x:=((0,0):ℝ×E))|>.eventually (gt_mem_nhds hp'))] with y hy hX
  refine ⟨duties _ h hy hX,fun z=>?_⟩
  by_cases H : z∈closedBall 0 r
  · have ht:= compel _ h (x:=y) hy hX (mem_closedBall_zero_iff.mp H); exact (composite ht (he _ (abs_le.mp ht.bound))).shimmy (Eventually.of_forall fun i=> indicator_of_mem H _)
  exact ((Brush.certified (x:=y) (k:=j) zero_le_one (0:ℝ)).climb (by rw [norm_zero]; exact hC) le_rfl).shimmy (Eventually.of_forall fun i=> indicator_of_notMem H _)

abbrev bulk (k : ℕ) (ϕ ψ : E×Poll.Body ι→ℝ) (ρ : E→Poll.Body ι) (M : E→Matrix ι ι ℝ) := mean k ((M 0)⁻¹) (nodes ϕ ψ ρ M)
lemma rates (hi : k ≤ j) {v' ε : ℝ} (hp : ∀ z : ι→ℝ,dotProduct z ((M 0)⁻¹*ᵥ z) ≤ v'*dotProduct z z) (hh : 1 ≤ D)
    (hg : Brush j c 1 Real.exp 0) (he : ∫ z in (closedBall (0:Y) D)ᶜ,(1+‖z‖)^zgrade j ∂Poll.sweep ((M 0)⁻¹) ≤ ε) :
    (∀ i, i ≤ k → Integrable (AuxConstant.moment U i) S) ∧
    bulk k ϕ ψ ρ M 0=1 ∧
    Brush k (clump j (fee j p D) c * ε) 1 (ratify ϕ ψ ρ M D - bulk k ϕ ψ ρ M) 0:= by
  have hD:= (h.gram 0 (by rw [norm_zero]; exact h.pos)).1.inv
  have ht := (buds h hh hg (0:Y)).nonneg; rw [norm_zero,add_zero,one_pow,mul_one] at ht
  have hf (D' : ℝ) (H:0≤D'): Meristem (truncate U D') 0 S k:= by
    obtain ⟨C,hC,hU⟩:= neighbors h H hh
    exact (Meristem.points (truncate U D') S ⟨fun _=> C, integrable_const _, hU.mono (fun y hy z=> ((hy.2 z).smaller hi))⟩ (hU.mono fun i hi=> hi.1)).1
  obtain ⟨ha,hX⟩:= AuxConstant.upgrades U hD hp ht hf (fun z=> (buds h hh hg z).smaller hi) he h.off
  refine ⟨ha,?_,hX⟩
  rw [bulk,(mean_at k U ha _).2]; simp_rw [blockTaylor_zero,nodes]; change (∫ z:Y, Real.exp (grace ϕ ψ ρ M z (0,0)) ∂ S)=_; simp [zeroC]
end YM.RGComparison01.AuxGrace
