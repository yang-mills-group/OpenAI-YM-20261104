import YM.FrontierTrace.Shear.Reference
/-!
# Quantitative trace from the two-radii comparison

No matrix estimate beyond the free scalar and coordinate costs. We exhibit
a smaller-error obligation on the narrow contrast (and K order zero). Error
bound survives factor `g^4` from squaring `trace`; permit any further payable
ε. `a` near 1 required at the read. See `Samples.lean` for filter uses.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.FrontierTrace
open Function Filter Set Analysis Trace MeasureTheory Table Climb
open Next.UVStress Work.A01
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace Interval

variable {G:Gauge} {C:Family G} {S:Table C.book}{f:Extraction.Order} (F:Spec.Final C f S)
    {r:ℝ} (ℓ:E4) (P:Spin.change S 4)

/-- Last physical Wilson frame comparison demand per scale r>0 (`g` the
 expansion variable). Fields and two generic-separated-point profiles, plus
 uniform cost on the scalar order-zero correl & offdiag scale factor. No estimate
 of coincidence terms. `ε` will be o(1) (any explicit power/log preferred).

The order-2 mixed-contrast estimate `interacting` is a major **unsupplied**
hypothesis, on vertex comparison through two in the X calculation against the
anomaly-pole `signal2` target. It's not a Ward tautology of these input moments.
Using `origin` rather than identifying any MS-bar normalization committedly;
producers must still fix/check WilsonX match realizing this signal from formal
coefficients. This record and results below do not claim the input proven.
-/
structure TwoRadii (r g ε a : ℝ) : Prop where
    paying : Paying F P
    frame : r^4 • F.sector.energy 0 1 = a • P (metric0 C.labels 0 1)
    stress : |a-1|≤ ε
    scalar (t:ℝ) : t∈[[(1:ℝ),2]] → ‖KK ℓ P r t - K0 G t‖ ≤ ε
    interacting : ‖signal ℓ P r - g^2 • (signal2 G:ℂ)‖ ≤ (g^2)*ε
-- all data on one S. no replacing bare J or coupling.

variable {g ε a:ℝ}
local notation "ι0" => determinant0 G
local notation "τ0" => candidate2 G
local notation "σ0" => signal2 G
local notation "A0" => theoryDensity G

omit F
lemma ordinate_budget {x y:ℂ}{p q:ℝ}{f:ℂ}{u:ℂ}{e a:ℝ}{δ η:ℝ} (hpx : p • x = (3/4:ℝ) • a • y)
    (hqu : q • u = (3/4:ℝ) • f) (he : |a-1| ≤ e) (hy: ‖y-f‖ ≤ δ)
    (hx : ‖x-u‖ ≤ η) (h : e ≤ 1) : ‖x‖ * |p-q| ≤ 2*δ + e*‖f‖ + |q| *η := by
    have he' : 0≤e:=(abs_nonneg _).trans he
    have hδ:0≤δ:=(norm_nonneg _).trans hy
    have ha : |a|≤ 2:= by obtain ⟨hA,ha⟩:=abs_le.mp he; exact abs_le.mpr ⟨by linarith,by linarith⟩
    have hg : (p-q) • x = (3/4:ℝ) • (a • (y-f)+(a-1) • f) - q • (x-u) := by
       rw [sub_smul,hpx,smul_sub q,sub_smul a]
       have hF:=hqu
       rw [hF]; module
    have hY : ‖a • (y-f)+(a-1) • f‖ ≤ 2*δ + e*‖f‖ := by
       refine (norm_add_le ..).trans (add_le_add ?_ ?_)
       · rw [norm_smul,Real.norm_eq_abs]; exact mul_le_mul ha hy (norm_nonneg _) zero_le_two
       rw [norm_smul,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_right he (norm_nonneg _)
    calc
       _ = ‖(p-q) • x‖:=by rw [norm_smul,Real.norm_eq_abs,mul_comm]
       _ ≤ 2*δ+e*‖f‖+‖q • (x-u)‖:=by
          rw [hg];
          refine (norm_sub_le ..).trans (add_le_add ?_ (le_refl _))
          rw [norm_smul_of_nonneg (by norm_num : (0:ℝ) ≤ 3/4)]
          exact (mul_le_of_le_one_left (norm_nonneg _) (by norm_num)).trans hY
       _ ≤ _:=by rw [norm_smul,Real.norm_eq_abs]; gcongr

noncomputable def determinantCost (G:Gauge) : ℝ:= (2+ |signal2 G| +49*|candidate2 G|) / (|determinant0 G|/2)
lemma determinantCost_pos (h:G.Simple) : 0<determinantCost G:=by unfold determinantCost; positivity [(determinant0_neg h).ne]

include F
variable (hG:G.Simple)(ℓ:E4)

theorem local_coefficient (h:TwoRadii F ℓ P r g ε a)(hG:G.Simple) (he:ExactTurns F) (hℓ:‖ℓ‖=1)(hne:ℓ 0*ℓ 1≠0)
    (hr:0<r) (hε:ε≤ |ι0|/98) (hv:ε ≤ 1) (d:ℝ)(hd:r^4 • centered F=(4*d) • scalarA P) :
    |d-τ0*g^2| ≤ (g^2)* ε * determinantCost G := by
   let x:= intervalView (KK ℓ P r); have h0: intervalView (K0 G)=(ι0:ℂ):= determinant_free G
   have hg:= stableView (pure_smooth F ℓ (scalarA P) hℓ hr) (K0_cont G) h.scalar
   rw [h0] at hg; change ‖x - (ι0:ℂ)‖ ≤ 49*ε at hg
   have ht: (τ0*g^2) • (ι0:ℂ)=(3/4:ℝ) • g^2 • (σ0:ℂ):=by
      simp only [Complex.real_smul,← Complex.ofReal_mul]; apply congr_arg ((↑):ℝ→ℂ)
      calc
        _ = g^2*(τ0*ι0):=by ring
        _ = _:=by rw [pole_consistent]; ring
   have hx := ordinate_budget (x:=x) (contrast F ℓ P he hG h.paying hℓ hne hr h.frame hd) ht h.stress h.interacting hg hv
   have hp : 0 < |ι0|/2:= by positivity [(determinant0_neg hG).ne]
   have hX : |ι0|/2 ≤ ‖x‖ := by
      have hz: ‖(ι0:ℂ)‖-‖x‖ ≤ ‖x-(ι0:ℂ)‖:= (norm_sub_norm_le ..).trans_eq (norm_sub_rev ..)
      rw [Complex.norm_real, Real.norm_eq_abs] at hz; linarith
   apply le_of_mul_le_mul_left (a:=(|ι0|/2)) _ hp; unfold determinantCost
   calc
      _ ≤ ‖x‖ * |d-τ0*g^2|:=mul_le_mul_of_nonneg_right hX (abs_nonneg _)
      _ ≤ _ := hx
      _ = _ := by rw [norm_smul_of_nonneg (by positivity : 0≤g^2), Complex.norm_real, Real.norm_eq_abs,
                        abs_mul, abs_of_nonneg (by positivity : 0 ≤ g^2)]; field_simp [(determinant0_neg hG).ne]

omit F in
lemma square_quote {x:Points 2}(A:S.Field 4)(b c:ℝ):
    custom x (b • A) (c • A) = (b*c) • custom x A A:=by
   obtain ⟨L,h⟩:= custom_linear (e:=4) x (c• A); obtain ⟨M,hM⟩:= cu_linear₂ (v:=A) (d:=4) x
   rw [h,show L (b • A)=b • L A from ((L.restrictScalars ℝ).map_smul ..), ← h,hM,hM,
       show M (c • A)=c • M A from ((M.restrictScalars ℝ).map_smul ..), smul_smul]

lemma unselected_quote {x:Points 2}(c:ℝ)(d:ℝ)(hd:c^4 • centered F=(4*d) • scalarA P):
    c^8 • central F none x=(4*d)^2 • custom x (scalarA P) (scalarA P):=by
   rw [raw_focus_exact,Trace.focus_eq]
   change c^8 • custom x (centered F) (centered F)=_
   rw [show c^8=c^4*c^4 by ring,← square_quote,hd,pow_two (4*d),← square_quote]

omit F hG in
lemma norm_square {p q : ℝ} {x y : ℂ} {k u v δ ε : ℝ} (hx : ‖y‖ ≤ k) (hp : |p| ≤ u) (ht:|q|≤v)
    (hr : |p-q| ≤ δ)(hv : ‖x-y‖≤ε): ‖(4*p)^2 • x-(4*q)^2 • y‖ ≤
           16*u^2*ε +16 * δ*(u+v)*k := by
   let P := |p|; let Q:= |q|; have h0 :0≤δ:= (abs_nonneg _).trans hr
   have hZ : |p+q| ≤ u+v:= (abs_add_le ..).trans (add_le_add hp ht)
   have hu : |(p^2-q^2)| ≤ δ*(u+v) := by
      rw [sq_sub_sq,abs_mul]; -- may factors reversed?
      rw [mul_comm |p+q|]; exact mul_le_mul hr hZ (abs_nonneg _) h0
   calc
     _ = ‖(4*p)^2 • (x-y)+(16*(p^2-q^2)) • y‖ := congr_arg norm (by module)
     _ ≤ ‖(4*p)^2 • (x-y)‖+‖(16*(p^2-q^2)) • y‖:= norm_add_le ..
     _ ≤ _ := by
       apply add_le_add
       · rw [norm_smul,Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
         apply mul_le_mul _ hv (norm_nonneg _) (by positivity)
         rw [mul_pow, ← sq_abs p, show (4:ℝ)^2=16 from by norm_num]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hp 2) (by norm_num)
       rw [norm_smul,Real.norm_eq_abs,abs_mul, abs_of_pos (by norm_num : (0:ℝ)<16)];
       have hp0:0≤ u+v:=(abs_nonneg _).trans hZ
       refine mul_le_mul ?_ hx (norm_nonneg _) (by positivity)
       exact (mul_le_mul_of_nonneg_left hu (by norm_num : (0:ℝ)≤16)).trans_eq (by ring)
end YM.FrontierTrace
