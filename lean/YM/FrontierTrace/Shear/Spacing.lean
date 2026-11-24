import YM.FrontierTrace.Shear.Rate
/-! Conditional error propagation (all x at the same spacing).
This uses the *unconditional* joint provider if needs Services on the given F,
no full-scheme or Gram estimates presumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.FrontierTrace
open Function Filter Set Analysis Trace MeasureTheory Table Climb OPE
open Next.UVStress Work.A01
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace Interval

variable {G:Gauge} {C:Family G} {S:Table C.book}{f:Extraction.Order} (F:Spec.Final C f S)
    {r:ℝ} (ℓ:E4) (P:Spin.change S 4)

lemma norm_conf {x:Points 2}{s:ℝ}(hs:0<s) (hx:‖x 1-x 0‖=s): x∈conf 2:=by
   rintro i j he
   have h0:x 1 ≠ x 0:=sub_ne_zero.mp (norm_ne_zero_iff.mp (hx.symm ▸ hs.ne'))
   fin_cases i <;> fin_cases j
   · rfl
   · exact (h0 he.symm).elim
   · exact (h0 he).elim
   rfl
lemma norm_shape (hℓ:‖ℓ‖=1) (hr:0<r) : let x:=atShape (r • ℓ);
    ‖x 1 - x 0‖=r := by intro x; change ‖0-(r • ℓ)‖=r; simp only [zero_sub,norm_neg,norm_smul_of_nonneg hr.le,hℓ,mul_one]
lemma band_geometry (hr:0<r)(x:Points 2)(t:ℝ)(ht:t∈[[(1:ℝ),2]])(h:‖x 1-x 0‖=r*t):
    WithinRoom r 2 1 x.ofLp (x 0) := by
   rw [uIcc_of_le (by norm_num)] at ht
   refine ⟨fun i=>?_,fun i j hij=>?_⟩
   · fin_cases i
     · simp; positivity
     change ‖x 1 - x 0‖ ≤ 2*r; rw [h]; linarith only [mul_le_mul_of_nonneg_left ht.2 hr.le]
   have hh:1*r ≤ ‖x 1-x 0‖:=by rw [h]; linarith only [mul_le_mul_of_nonneg_left ht.1 hr.le]
   fin_cases i <;> fin_cases j
   · contradiction
   · rw [norm_sub_rev]; exact hh
   · exact hh
   contradiction

def weight0 (G:Gauge):ℝ:= 16*(|candidate2 G|+determinantCost G)^2 +
      16*determinantCost G*(determinantCost G+2*|candidate2 G|)*Trace.theoryDensity G
lemma weight0_pos (h:G.Simple):0 < weight0 G := by
   unfold weight0; positivity [candidate_negative h, determinantCost_pos h, theoryDensity_pos h]
local notation "ϰM"=>determinantCost G
local notation "B"=>candidate2 G
variable {g a ε:ℝ}
set_option maxHeartbeats 500000 in
theorem at_band (h:TwoRadii F ℓ P r g ε a)(hG:G.Simple) (he:ExactTurns F) (hℓ:‖ℓ‖=1)(hne:ℓ 0*ℓ 1≠0)
    (hr:0<r) (hε:ε≤ |determinant0 G|/98) (hv:ε ≤ 1) (t:ℝ)(ht:t∈[[(1:ℝ),2]]) : ∀ x:Points 2, ‖x 1-x 0‖ = r*t →
     ‖r^8 • (central F none x) - (g^4 • (4*B)^2 • K0 G t)‖ ≤ (g^4)*ε*weight0 G:=by
   obtain ⟨d,hd⟩:= centered_quote F P h.paying hG r
   have hP := local_coefficient F P ℓ h hG he hℓ hne hr hε hv d hd -- argument order
   have ha := h.scalar t ht
   have hy: 0<r*t:= mul_pos hr (zero_lt_one.trans_le (show 1≤t from by rw [uIcc_of_le (by norm_num)] at ht; exact ht.1))
   let u:=r*t; let y:=atShape (u • ℓ)
   intro x hX; have heq: central F none x = central F none y:= by
      have hh:= Trace.θ_norm_rep F x (norm_conf hy hX); have hw:=Trace.θ_norm_rep F y (atRoom (aim_ne ℓ hℓ u hy)); have hu: ‖y 1-y 0‖=u:=norm_shape ℓ hℓ hy
      rw [hu] at hw; rw [hX] at hh; exact hh.trans hw.symm
   rw [heq,unselected_quote F P r d hd]
   change ‖(4*d)^2 • KK ℓ P r t-g^4 • _‖ ≤ _
   have hs: g^2* ε*ϰM ≤ g^2*ϰM := by nlinarith [determinantCost_pos hG,mul_nonneg (mul_nonneg (sq_nonneg g) (determinantCost_pos hG).le) (sub_nonneg.mpr hv)]
   have ht' : |B*g^2| ≤ g^2 * |B| := (abs_mul ..).le.trans_eq (by rw [abs_of_nonneg (sq_nonneg g),mul_comm])
   have hl : |d| ≤ g^2*(|B|+ϰM) := by
      have hw:= (abs_add_le (d-B*g^2) (B*g^2)).trans (add_le_add (hP.trans hs) ht')
      rw [sub_add_cancel] at hw; exact hw.trans_eq (by ring)

   rw [smul_smul, show g^4 * (4*B)^2 = (4*(B*g^2))^2 by ring]
   apply (norm_square (K0_norm hG t ht) hl ht' hP ha).trans_eq
   unfold weight0; ring

-- any phase and uniform on a comparable-scale annulus.
theorem all_band (H:Services C f S) (he:ExactTurns F) (hℓ:‖ℓ‖=1)(hne:ℓ 0*ℓ 1≠0):
    ∀ᶠ r:ℝ in 𝓝[>]0, ∀ (ε g a:ℝ) (P:Spin.change S 4), ε ≤ |determinant0 G|/98 → ε≤ 1→
    TwoRadii F ℓ P r g ε a → ∀ (t:ℝ)(x:Points 2)(p:Viewers F), t∈[[(1:ℝ),2]]→‖x 1-x 0‖=r*t→
    ‖r^8 • central F p x - g^4 • (4*B)^2 • K0 G t‖ ≤
       r^8*(2*(cape F)^2+2*r^(-7.5:ℝ)) +(g^4)*ε*weight0 G := by
   -- all r filter pays phase error not spent before ε from actual construction.
   filter_upwards [(centered_phased F H (M:=2) (η:=1) (ε:=0.5) zero_le_two (by norm_num) one_pos), self_mem_nhdsWithin (s:=Ioi (0:ℝ))] with r hV (hr:0<r) ε g a P hε hε' ht t x p hu hx
   have hY:=hV x (x 0) (band_geometry hr x t hu hx) p none; rw [show (-7:ℝ)-0.5= -7.5 by norm_num] at hY
   calc
       _ ≤ ‖(r^8:ℝ) • central F p x-r^8 • central F none x‖+‖r^8 • central F none x-g^4 • (4*B)^2 • K0 G t‖:=norm_sub_le_norm_sub_add_norm_sub ..
       _ ≤ _:= add_le_add (by rw [← smul_sub,norm_smul_of_nonneg (pow_pos hr 8|>.le)]; exact mul_le_mul_of_nonneg_left hY (by positivity)) (at_band F ℓ P ht H.simpleGate he hℓ hne hr hε hε' t hu x hx)
end YM.FrontierTrace
