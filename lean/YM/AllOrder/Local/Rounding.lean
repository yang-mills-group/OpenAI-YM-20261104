import YM.AllOrder.Local.Taylor
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lantern.Lens

/-!
# Costs at an anchor and rescaling/proving arbitrary jets there

All orders share the same Gaussian for Laplace votes; shrinking the real
external/g parameter stencil as the displacement grows is free here (pointwise
for moments); doesn't assume analyticity of full pushed log at zero coupling.
Each **uncut** moment integrates a polynomial-growth function. Flat cost for
cutoff moments will follow from the Gaussian tail, not by discarding it.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Local.Vote
open Function Filter Set Matrix Metric MeasureTheory ProbabilityTheory
open Lattice Wilson RG Gauge Input Pressure Push.AbsoluteSums
open ConnectedActivityE6 Blaze Brush PhysicalNext Repeat Lantern Poll
open scoped Topology Classical ContDiff ENNReal

lemma cl (j:ℕ) {a b c:ℝ} (h : 0≤a) (he : 0 ≤ b) (hc : 1 ≤ c) :
    0 ≤ clump j a b ∧ clump j (a*c) b ≤ clump j a b * c^j := by
  unfold clump; constructor; · positivity
  rw [mul_assoc (j.factorial*b), ←mul_pow]; gcongr; nlinarith

lemma cm (j:ℕ) {a b c:ℝ} (h : 0≤a) (he : 0 ≤ b) (hc : a ≤ c) : clump j a b ≤ clump j c b := by unfold clump; gcongr

lemma fn (j:ℕ) {p D:ℝ} (h : 0 ≤ p) (ht : 0≤D) : 0 ≤ fee j p D := by unfold fee acrossE spanE clump; positivity

lemma fee_increase (j:ℕ) {p D r:ℝ} (h : 0 ≤ p) (ht : 0≤D) (hr : 1 ≤ r) : fee j p (D*r) ≤ fee j p D * r^(j+2) := by
  have he : 0 ≤ spanE p (D*r):= by unfold spanE; have : 0≤r:=zero_le_one.trans hr; positivity
  have hk : 0 ≤ spanE p D:= by unfold spanE; positivity
  have ha : spanE p (D*r) ≤ spanE p D * r:= by unfold spanE; nlinarith
  set A := clump j (spanE p D) p
  set a := clump j (spanE p (D*r)) p
  obtain ⟨hp,hc⟩:= cl j hk h hr
  have hg : 0 ≤ A:=hp
  have hv : a ≤ A*r^j:=(cm _ he h ha).trans hc
  have hh : a ≤ A*r^(j+2):=hv.trans (by gcongr; omega)
  set Q:= D*r
  have hQ:0 ≤ Q:= mul_nonneg ht (zero_le_one.trans hr)
  have hp' : p ≤ p*r^(j+2):=le_mul_of_one_le_right h (one_le_pow₀ hr)
  unfold fee acrossE; change p+p+(Q*(Q*a)+Q*(Q*a))+(a+a)≤(p+p+(D*(D*A)+D*(D*A))+(A+A))*_
  have hs : Q*(Q*a) ≤ D*(D*A)*r^(j+2):= le_trans (b:=Q*(Q*(A*r^j))) (by gcongr) (le_of_eq (by unfold Q; ring_nf))
  linarith only [hs,hp',hh]

lemma clump_fee (j:ℕ) {p D r C : ℝ} (h : 0 ≤ p) (ht : 0 ≤ D) (hr : 1 ≤ r) (he : 0 ≤ C) :
    clump j (fee j p (D*r)) C ≤ clump j (fee j p D) C * r^((j+2)*j) := by
  rw [pow_mul]; exact (cm _ (fn j h (mul_nonneg ht (zero_le_one.trans hr))) he (fee_increase j h ht hr)).trans (cl j (fn j h ht) he (one_le_pow₀ hr)).2

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] 
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {φ ψ : E × Body ι → ℝ} {ρ : E → Body ι} {M : E → Matrix ι ι ℝ}
variable {j k : ℕ} {p c u v D C : ℝ} {x : ℝ × E} {z : Body ι}
variable (h : Golf φ ψ ρ M j D u v p)
include h
lemma golf_cost : 0≤p:= (h.curve _ (norm_zero.trans_lt h.pos)).nonneg

lemma golf_less (hh : k ≤ j) : Golf φ ψ ρ M k D u v p :=
  ⟨h.pos,h.pos',h.small,h.small',h.off,fun x hx=> (h.curve x hx).smaller (by omega),fun z t y hz ht hy hY=> by obtain ⟨hp,hg⟩:= h.color z t y hz ht hy hY; exact ⟨hp.smaller (by omega),hg.smaller hh⟩, h.station,fun x hx=> ⟨(h.gram _ hx).1,(h.gram _ hx).2.smaller hh⟩⟩

lemma golf_small (hp : 0<c) (hu : c ≤ u) (hv : c ≤ v) : Golf φ ψ ρ M j D c c p :=
  ⟨hp,hp,hu.trans h.small,hv.trans h.small',h.off,fun x hx=>h.curve x (hx.trans_le hu),fun z t y hz ht hy hY=> h.color z t y hz ht (hy.trans_le hv) (hY.trans_le hu),fun _ hx=> h.station _ (hx.trans_le hu),fun x hx=> h.gram x (hx.trans_le hu)⟩

lemma golf_high (hc : 1≤c) : Golf φ ψ ρ M j (D*c) u (v/c) p := by
  have h':0<c:=zero_lt_one.trans_le hc; have hr:=h.off
  refine ⟨h.pos,div_pos h.pos' h',h.small,(div_le_self h.pos'.le hc).trans h.small',by positivity,h.curve,?_,h.station,h.gram⟩
  intro z t x hx hy ht hv; let y:=(x.1*c,x.2); let z':= c⁻¹ • z
  have hz: ‖z'‖≤D:=by unfold z'; rw [norm_smul,Real.norm_of_nonneg (by positivity)]; grw [hx]; apply le_of_eq; field_simp -- use inequalities
  have hk: ‖y.1‖<v:= by change ‖x.1*c‖ < v; rwa [norm_mul,Real.norm_of_nonneg h'.le, ← lt_div_iff₀ h']
  have he : visit ρ z t x=visit ρ z' t y:= by unfold visit y z'; rw [show ((x.1*c,x.2)).1 • c⁻¹ • z=x.1 • z from (by rw [smul_smul,show (x.1*c)*c⁻¹=x.1 by field_simp])]
  rw [he]; exact h.color z' t y hz hy hk hv

variable [FiniteDimensional ℝ E]
lemma at_origin_bound (hD : 1 ≤ D) (C : ℝ) (he : Brush j C 1 Real.exp 0) (z : Body ι) :
    Brush j (clump j (fee j p D) C * (1+‖z‖)^((j+2)*j)) 1 (Real.exp ∘ grace φ ψ ρ M z) 0 := by
  set m:=1+‖z‖
  have hm : 1 ≤ m:=le_add_of_nonneg_right (norm_nonneg _)
  have h':= golf_high h hm
  have hv : ‖z‖ ≤ D*m:= (le_add_of_nonneg_left zero_le_one).trans (le_mul_of_one_le_left (zero_le_one.trans hm) hD)
  have hh := compel (x:=(0,0)) (D*m) h' (norm_zero.trans_lt h'.pos) (norm_zero.trans_lt h'.pos') hv
  exact (composite hh (by rw [zeroC]; exact he)).climb (clump_fee _ (golf_cost h) h.off hm he.nonneg) le_rfl

-- Truncated balls can be any size. Don't demand same project budget for their
-- exponent throughout the original x and b windows. Needed locally only.
omit [FiniteDimensional ℝ E] in
lemma golf_shrink : ∃ m : ℝ,
    Golf φ ψ ρ M j D m m p ∧ fee j p D * max m m ≤ 1 := by
  let k:=fee j p D
  have hk : 0 ≤ k:= fn _ (golf_cost h) h.off
  let c:= (1+k)⁻¹; have hc : 0<c:= inv_pos.mpr (by linarith)
  let z:= min c (min u v)
  have hz : z ≤ min u v := min_le_right ..
  refine ⟨z, golf_small h (lt_min hc (lt_min h.pos h.pos')) (hz.trans (min_le_left ..)) (hz.trans (min_le_right ..)),?_⟩
  rw [max_self]; change k*z≤1; refine (mul_le_mul_of_nonneg_left (min_le_left ..) hk).trans ?_; unfold c
  rw [← div_eq_mul_inv,div_le_one (by linarith)]; linarith

variable (μ : Measure (Body ι)) [IsFiniteMeasure μ]
lemma bushes : Meristem (ballots φ ψ ρ M D) (0:ℝ×E) μ j := by
  -- prove for any regularity order through Golf j. j=0 use j≥1 hypothesis later? amity requires hj≥1; bound exp at grace via Brush.bound not shrinking.
  have hh: ∀ᶠ y:ℝ×E in 𝓝 0, ‖y.2‖<u ∧ ‖y.1‖<v := ((continuous_norm.comp continuous_snd).continuousAt.eventually (gt_mem_nhds (norm_zero.trans_lt h.pos))).and ((continuous_norm.comp continuous_fst).continuousAt.eventually (gt_mem_nhds (norm_zero.trans_lt h.pos')))
  let c:=fee j p D
  obtain ⟨C,hC,hg⟩:= Brush.compact (f:=Real.exp) (k:=j) (s:=Icc (-c) c) isCompact_Icc fun y _=> Real.contDiff_exp.contDiffAt
  let A:=clump j c C
  have h': 0 ≤ A:= (cl (c:=1) _ (fn _ (golf_cost h) h.off) hC.le le_rfl).1
  let V:=ballots φ ψ ρ M D
  have hv: ∀ᶠ y in 𝓝 (0:ℝ×E), ∀ z, Brush j A 1 (fun y=> V y z) y := by
    filter_upwards [hh] with y hy z
    by_cases he:z ∈ closedBall (0:Body ι) D
    · have hx:= compel _ h hy.1 hy.2 (mem_closedBall_zero_iff.mp he)
      exact (composite hx (hg _ (abs_le.mp hx.bound))).shimmy (Eventually.of_forall fun _=>indicator_of_mem he _)
    exact ((Brush.certified zero_le_one (0:ℝ)).climb (show ‖(0:ℝ)‖ ≤ A from norm_zero.trans_le h') le_rfl).shimmy (Eventually.of_forall fun _=> indicator_of_notMem he _)
  exact (Meristem.points V μ ⟨fun _=> A, integrable_const _,hv⟩ (hh.mono fun i hi=> duties D h hi.1 hi.2)).1

end YM.AllOrder.Local.Vote
