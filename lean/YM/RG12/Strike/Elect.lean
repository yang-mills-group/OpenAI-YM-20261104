import YM.RG12.Strike.Film
import Mathlib.Algebra.Polynomial.Roots
/-! # Menu on first-order probes (two marks only, pointwise)

Write complete amplitude prolifically (finset/list finite closure); normalization scheme
P_b and orientation corrections can be offered just by lists of local terms *holding exact
engineering dimensions*, no Ward assumptions. All formulas are complex. Discrete subgroup
characters and phases only appear in their supplied continuum expansion comparisons, not here.
 Primary conversion identification (that A or Position or WilsonX recipes actually have
a reading expressible by these lists with the scheme conventions and exact term coefficients) is a
separate obligation and not proved here! Our claim is continuity/price law on precisely these
independently evaluable derivative kernels; it DOESN'T discharge the overall prescription.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Strike
open Function Set Filter MeasureTheory Real Finset
open scoped Topology InnerProductSpace ContDiff BigOperators Classical
-- wires begin at first mark & end at second, displacement z = first minus second or second minus
-- first depending routing; spin at first. signs for derivative in second absorb into constant.
-- include general normalization factor after these normalized D(x) wires.
variable (U V:Foil)(L K:Poke)
def ribbon (z:R):ℂ:=∑ i:Axis4,∑ j:Axis4, 2*U i j*barrage (cloud V K j) (L++[i]) z
lemma ribbon_holds: Garden (ribbon U V L K) (L.length+K.length+4):=by
  constructor
  · intro x hx; unfold ribbon; exact ContDiffAt.sum (s:=Finset.univ) (fun i _=> ContDiffAt.sum (s:=Finset.univ) (fun j _=>contDiffAt_const.mul (vellum punct_open (cloud_silk V K j) _ x hx)))
  intro y hy t ht
  unfold ribbon; simp only [ridges _ _ _ _ _ (show y∈puncture from hy), ridges _ _ _ _ _ (show t•y∈puncture from smul_ne_zero ht.ne' hy)]
  simp only [mul_sum, scaling _ y hy t ht, List.length_append,List.length_cons,List.length_nil]
  apply sum_congr rfl; intro p _;apply sum_congr rfl; intro q _; apply sum_congr rfl; intro r _; push_cast; ring_nf
-- local P/first correction: an open potential jet with curvature-curl exterior transforms with sum of
-- weight (potential weight L.length+1, opposite mark slot weight K.length+2).
def cord (j:Axis4)(x:R):ℂ:=barrage (cloud V K j) L x
lemma cord_held(i:Axis4): Garden (cord V L K i) (L.length+K.length+3):=by convert (Garden.lineage V K i []).roam L using 1 <;> first | rfl | simp only [List.length_nil,Nat.zero_add]; omega

-- k3 integrals convergence. Full Wick sign and constants external to local frost chart.
def basin (χ:R→ℂ)(U V W:Foil)(L T S:Poke)(i j:Axis4)(z:R):ℂ:= (1-χ z)*leg U L j [i] z*leg V T i [] z * leg W S j [] z
def tank (χ:R→ℂ)(U V W:Foil)(L T S:Poke) :ℂ:= ∑ i:Axis4,∑ j:Axis4, ∫ z:R,basin χ U V W L T S i j z
variable (W:Foil)(S:Poke)(χ:R→ℂ)(hχ:Base χ)(i j:Axis4)
include hχ
lemma tank_abs: Integrable (basin χ U V W L K S i j):=by
   let F:= leg U L j [i]*leg V K i []*leg W S j []
   let H:=L.length+K.length+S.length+10
   have h : Garden F H:=by convert ((Garden.lineage U L j [i]).times (Garden.lineage V K i [])).times (Garden.lineage W S j []) using 1; simp; omega
   obtain ⟨D,hD,he⟩:= h.outer 0
   have hU := hχ.head.eq_of_nhds
   let Z:R→ℂ:=basin χ U V W L K S i j; have hh(x:R):Z x = (1-χ x)*F x:=by unfold Z basin F;dsimp only [Pi.mul_apply]; ring
   have hC:Continuous Z:=continuous_iff_continuousAt.mpr (fun x=> by
       by_cases hx:x=0
       · subst x; have hf : Z =ᶠ[𝓝 (0:R)] 0:= hχ.head.mono fun x hx=>by simp [hh,hx]
         exact continuousAt_const.congr hf.symm
       rw [funext hh];exact (continuousAt_const.sub hχ.continu.continuousAt).mul (h.openSite x hx).continuousAt)
   let A(z:R):=((1+‖z‖)^6)⁻¹
   apply (hC.locallyIntegrable).integrable_of_isBigO_cocompact (g:=A) (Asymptotics.isBigO_iff.mpr ⟨D,?_⟩) (Integrable.integrableAtFilter ?_ _)
   · have hh' := hχ.compact
     rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at hh'
     filter_upwards [hh', he] with x hx hy
     change ‖Z x‖≤ D*‖A x‖
     rw [hh,show χ x= 0 from hx,sub_zero,one_mul,Real.norm_of_nonneg (by unfold A; positivity),← div_eq_mul_inv] -- A unfold req
     apply (show ‖F x‖ ≤ _ by simpa only [sub_zero] using hy).trans -- metav
     have hx :1 ≤1+‖x‖:=by linarith only [norm_nonneg x]
     gcongr; unfold H; omega
   have he : Integrable (fun z:R=> (1+‖z‖)^(-((6:ℕ):ℝ))) :=integrable_one_add_norm (by norm_num)
   simp_rw [Real.rpow_neg_natCast,zpow_neg,zpow_natCast] at he; exact he
omit hχ
-- homogeneous response arm. `Wire` encompasses also read from constant gradient and auxiliary
-- first-order contact terms ± equality by literal amplitude not ghost tampering. Can take negative
-- argument on all arms before assembling.
variable {b c H:ℕ}{F G:R→ℂ}(x:R)(hx:x≠0)
lemma Garden.rear (hf:Garden F b) : Garden (fun y:R=>F (-y)) b:=by
  refine ⟨fun x hx=> ContDiffAt.comp (g:=F) (f:=fun x:R=>-x) _ (hf.openSite (-x) (neg_ne_zero.mpr hx)) contDiffAt_id.neg, fun x hx r hr=>?_⟩
  rw [← smul_neg]; exact hf.line (-x) (neg_ne_zero.mpr hx) r hr
include hx
lemma Garden.drawHold (hf:Garden F b)(h:b≤H):Waive H (Gap x H F) := by
   apply (Waive.monomial (-F x) (H-b) (Nat.sub_le H b)).congr
   intro t ht; unfold Gap; rw [hf.radial hx ht]; have hv:(t:ℂ)≠0:=by exact_mod_cast ht.ne'
   nth_rw 2 [show H = H-b+b from (Nat.sub_add_cancel h).symm] -- distribution
   rw [pow_add, inv_pow];field_simp;ring
lemma Garden.spectates (hf:Garden F b)(h:Waive c (Gap x c G)): Waive (b+c) (Gap x (b+c) (F*G)) := by
   apply ((h.upper (show c≤b+c from Nat.le_add_left ..)).credit (F x)).congr
   intro t ht; unfold Gap; rw [Pi.mul_apply, Pi.mul_apply, pow_add,hf.radial hx ht, inv_pow]; have hv:(t:ℂ)≠0:=by exact_mod_cast ht.ne'
   field_simp
omit hx in
lemma empties (t:ℂ) : Waive b (Gap x b (fun _=>t)):= by
   apply (Waive.monomial (-t) b (le_rfl (a:=b))).congr
   intro r _; unfold Gap; ring

-- close list. letter inputs/spin/color polars all included in outer coefficient χ. no wave eq premise.
inductive First : ℕ→ (R→ℂ) → Prop where
 | nil(k:ℕ): First k 0
 | weight {k : ℕ} {F:R→ℂ}: First k F → (v:ℂ)→First k (fun x=>v*F x)
 | join {k:ℕ} {F G:R→ℂ}: First k F → First k G → First k (F+G)
 | turn {k:ℕ} {F:R→ℂ}: First k F → First k (fun y:R=>F (-y))
 -- accept *known* strictly-lower (and equal) homogeneous arm terms including local P and
 -- any filtered-frame derivative evaluated at free order. Can include convolution of c terms by escalation,
 -- but needn't estimate products of two nonhomogeneous fields at order one.
 | classV {k p:ℕ} {F:R→ℂ}: p≤k→Garden F p→ First k F
 -- tank term (strict, since k ≥ 6 in application)
 | dam (χ:R→ℂ) (U V W:Foil)(L K S:Poke) : Base χ→First (profile L K S) (fun _=>tank χ U V W L K S)
 | core (χ:R→ℂ) (U V W:Foil)(L K S:Poke)(θ:Farm): anti U→ anti V→ anti W→Base χ→First (profile L K S) (gala U V W L K S χ θ)
 | wire {b c:ℕ} {F G:R→ℂ}: Garden F b→ First c G→First (b+c) (F*G)
-- rank demands at all point orientations. arm-inflation derivative not applied to integrated coefficient here,
-- use differentiating inputs before attaching, or prove further Ward normalization.
theorem exacted (h:First b F):Waive b (Gap x b F):=by
   induction h generalizing x with
   | nil b=> unfold Gap;simp only [Pi.zero_apply,mul_zero,sub_zero]; exact Waive.nada _
   | weight _ i he=>
      apply ((he x hx).credit i).congr
      intro t _; unfold Gap; ring
   | join _ _ ha hb=>
      apply ((ha x hx).merge (hb x hx)).congr
      intro t _; unfold Gap; simp only [Pi.add_apply]; ring
   | turn _ he=>
      apply (he (-x) (neg_ne_zero.mpr hx)).congr
      intro t _; unfold Gap; rw [smul_neg]
   | classV h hp=> exact hp.drawHold x hx h -- order
   | dam _ _ _ _ _ _ _ _=> exact empties ..
   | core _ _ _ _ _ _ _ _ h1 h2 h3 h4=> exact fiesta _ _ _ _ _ _ _ x _ h4 hx h1 h2 h3
   | wire he _ _=> exact he.spectates x hx (by solve_by_elim) -- order
-- detection of missing log price on unscaled engineering. test on any open Ioo 1 K
omit hx in
lemma no_coupon (c:ℂ){h:ℝ→ℂ}(he:Waive b h){m:ℝ}(hm:1 < m)(hC:∀ t∈Ioo (1:ℝ) m,h t=(Real.log t:ℂ)*c): c=0:=by
    let k:=(1+m)/2; have hk:1<k:=by unfold k; linarith
    have hk0:0<k:=zero_lt_one.trans hk
    obtain ⟨f,hf⟩:=he
    let w(i:Fin b):ℂ:=f i*((k:ℂ)^(i.val+1)-1)
    let z:=(Real.log k:ℂ)*c
    let D:Polynomial ℂ:= Polynomial.C z - ∑ i:Fin b, Polynomial.C (w i) * Polynomial.X^(i.val+1)
    let V:=Ioo 1 (m/k)
    have hv: (1:ℝ)<m/k:=by rw [lt_div_iff₀ hk0,one_mul]; unfold k; linarith
    have hd: Set.Infinite (Complex.ofReal '' V):=(Set.Ioo_infinite hv).image (Complex.ofReal_injective.injOn) -- theorem
    have hΨ : D=0:=Polynomial.eq_zero_of_infinite_isRoot _ (hd.mono (by
      rintro r ⟨t,⟨h₁,h₂⟩,rfl⟩
      have h3:t<m:=h₂.trans_le (div_le_self (zero_lt_one.trans hm).le hk.le)
      have ht:0<t:=zero_lt_one.trans h₁
      have hL:k*t<m:=by rw [mul_comm];exact (lt_div_iff₀ hk0).mp h₂
      have hr:k*t>1:= by nlinarith
      have hh:= hC t ⟨h₁,h3⟩; have h_:= hC (k*t) ⟨hr,hL⟩
      rw [hf _ ht] at hh -- fix
      rw [hf _ (by positivity),Complex.ofReal_mul,Real.log_mul hk0.ne' ht.ne',Complex.ofReal_add,add_mul, ← hh] at h_
      simp only [mul_pow] at h_
      change D.IsRoot (t:ℂ)
      simp only [Polynomial.IsRoot,D, Polynomial.eval_sub,Polynomial.eval_C,Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X]
      rw [show (∑ i:Fin b,_) = (∑ i:Fin b, f i*((k:ℂ)^(i.val+1)*(t:ℂ)^(i.val+1)-1)) - ∑ i:Fin b, f i*((t:ℂ)^(i.val+1)-1) from ?_, h_]; ring
      rw [← Finset.sum_sub_distrib]; refine sum_congr rfl (fun i _=>?_); unfold w; ring))
    have hi:= congrArg (Polynomial.eval (0:ℂ)) hΨ
    simp [D, Polynomial.eval_finsetSum] at hi
    exact (mul_eq_zero.mp hi).resolve_left (by exact_mod_cast (Real.log_pos hk).ne') -- after simp yields z
end YM.RG12.Strike
