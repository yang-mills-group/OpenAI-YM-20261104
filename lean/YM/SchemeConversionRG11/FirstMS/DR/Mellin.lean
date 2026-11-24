import YM.SchemeConversionRG11.FirstMS.DR.Layers
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Local homogeneity continuation (position prescription, no global CT conflicts in this test).
The measure factor analytic with any other compact integration prefactors is included in the shell
kernel `F`. `age` for pair subgraph with coincidence degree n:
AF-AF D dimensional weights `(D-1)+(D-1)`, need n=2. ∂AF-AF one higher, n=3. -/

set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.DR
open Function Set Filter MSbar MSbar.Dim MSbar.Symbol MeasureTheory Metric Complex intervalIntegral
open scoped Topology ContDiff Classical

private lemma peels_AH {u:Set ℂ} (hu:IsOpen u) {F:ℂ×ℝ → ℂ} (h:AH u F) (n:ℕ):
    AH u (fun p:ℂ×ℝ=> layer n (fun t=> F (p.1,t)) p.2) :=
    ((h.arguments (w:=Prod.snd) (tame_projR (X:=ℝ))).rad_tail n hu).arguments
       (w:=fun t:ℝ=> ((0:ℝ),t)) (tame_pair (HasTemperateGrowth.const _) (by fun_prop))

-- Integral against smooth AH weight, or cpow with strictly positive real part
private lemma legato {u:Set ℂ} (hu:IsOpen u) (w:ℝ × ℂ→ℂ){R:ℝ} (_ : 0≤R)
   (hw : ContinuousOn w (Icc 0 R ×ˢ u)) (hm : ∀ a∈ Icc 0 R,DifferentiableOn ℂ (fun z:ℂ=>w (a,z)) u)
   {f : ℂ×ℝ→ℂ} (hf:AH u f) : AH u (fun p:ℂ×ℝ=> ∫ t in Ioc 0 R,w (t,p.1)*f (p.1,t)):= by
   let g (p:ℂ×ℝ×ℝ):=f (p.1,p.2.2)
   have hg:AH u g:= hf.arguments tame_projR
   refine (AH.cauchy_average (μ:=volume) hu hg continuous_id isCompact_Icc hw hm).congr hu (fun z hz x=> integral_Icc_eq_integral_Ioc) -- implicit? hr unused

lemma weight_ok {u:Set ℂ} (hu:IsOpen u) {R:ℝ} (hr:0≤R) {q:ℂ→ℂ}
   (hq : ∀ z∈u,DifferentiableAt ℂ q z) (hp:∀ z∈u,0 < (q z).re)
   {f:ℂ×ℝ→ℂ} (h:AH u f) : AH u (fun p:ℂ×ℝ=> ∫ t in Ioc 0 R,(↑t:ℂ)^(q p.1)*f (p.1,t)):= by
   let w (p:ℝ × ℂ):ℂ:= (p.1:ℂ)^(q p.2)
   apply legato hu w hr _ _ h
   · intro v hv
     exact ((Complex.continuousAt_ofReal_cpow v.1 _ (Or.inl (hp v.2 hv.2))).comp (f:=fun p:ℝ × ℂ=> (p.1,q p.2)) (continuousAt_fst.prodMk (((hq v.2 hv.2).continuousAt).comp continuousAt_snd))).continuousWithinAt
   intro a _ z hz; change DifferentiableWithinAt ℂ (fun z => (↑a:ℂ)^(q z)) _ _
   exact ((hq z hz).const_cpow (Or.inr (fun ht=> absurd (hp z hz) (by rw [ht];simp)))).differentiableWithinAt

lemma bare_weight {u:Set ℂ}(hu:IsOpen u){R:ℝ}(hr:0≤R){f:ℂ×ℝ→ℂ}(h:AH u f) : AH u (fun p:ℂ×ℝ=> ∫ t in Ioc 0 R,f (p.1,t)) := by
    refine (legato hu (fun _=> 1) hr continuousOn_const (fun _ _=>differentiableOn_const 1) h).congr hu ?_
    intro z hz x; simp

variable {F:ℂ×ℝ → ℂ} {R:ℝ}

/-- General continuous radial Mellin fit with ν measure.
 Ordinary uses exponent ν−1; subtract power shells only on sets away from t=0. -/
def rent (F:ℂ×ℝ→ℂ)(R:ℝ)(n:ℕ)(z ν:ℂ):=
    (∫ t in Ioc 0 R,(t:ℂ)^(ν+n-1)*layer n (fun t=> F (z,t)) t)+
      ∑ j∈Finset.range n, (R:ℂ)^(ν+j)/(ν+j)*layer j (fun t=> F (z,t)) 0

variable {u:Set ℂ}
include F
lemma pays {z ν:ℂ} (hR:0<R) (hν:0<ν.re) (hz : z∈u) (h:AH u F) (n:ℕ) :
    rent F R n z ν = ∫ t in Ioc 0 R,(t:ℂ)^(ν-1)*F (z,t) := by
   let t(j:ℕ)(x:ℝ):= (↑x:ℂ)^(ν+j-1)
   have hr(j:ℕ) : 0<(ν+j).re:= by simp; positivity
   have hi(j:ℕ) : IntervalIntegrable (t j) volume 0 R := intervalIntegrable_cpow' (by simp; positivity)
   let f(x:ℝ):=F (z,x)
   have hf(j:ℕ): ContDiff ℝ ∞ (layer j f) := (layer_tame_ray j (h.slice hz)).1
   have he(j:ℕ): (R:ℂ)^(ν+j)/(ν+j)=∫ x in (0:ℝ)..R,t j x := by
      unfold t; rw [integral_cpow (Or.inl (show -1 < ((ν+(j:ℂ))-1).re by simp; positivity))]
      rw [sub_add_cancel, ofReal_zero, zero_cpow (show ν+(j:ℂ)≠0 from fun he => by have HH:=hr j; rw [he] at HH; exact lt_irrefl _ HH),sub_zero]
   let a(j:ℕ)(x:ℝ) := t j x * layer j f 0
   have ha(j:ℕ) : (R:ℂ)^(ν+j)/(ν+j)*layer j f 0 = ∫ x in Ioc 0 R,a j x := by
      unfold a; rw [MeasureTheory.integral_mul_const,← intervalIntegral.integral_of_le hR.le,←he]
   unfold rent; change _+(∑ j∈ Finset.range n,_ * layer j f 0) = _
   have aw (j : ℕ) : Integrable (a j) (volume.restrict (Ioc 0 R)) := ((hi j).mul_const _).1
   simp_rw [ha]
   rw [← MeasureTheory.integral_finsetSum _ (fun j _=> aw j)]
   change (∫ x in Ioc 0 R, t n x*layer n f x) + _ = _
   have hb: Integrable (fun x=> ∑ j∈Finset.range n,a j x) (volume.restrict (Ioc 0 R)):= integrable_finsetSum _ fun j _=> aw j
   rw [← MeasureTheory.integral_add ((hi n).mul_continuousOn (hf n).continuous.continuousOn).1 hb]
   apply setIntegral_congr_fun measurableSet_Ioc; intro x hx
   conv_rhs=> dsimp only; rw [show F (z,x)=_ from strip_pow f n x,mul_add,Finset.mul_sum]
   have hX : (↑x:ℂ)≠0 := ofReal_ne_zero.mpr hx.1.ne'
   have hk(j:ℕ)(a:ℂ): t j x*a = (x:ℂ)^(ν-1)*((x:ℂ)^j*a):= by unfold t; rw [add_sub_right_comm, cpow_add _ _ hX,cpow_natCast,mul_assoc]
   change t n x*_ + ∑ j∈Finset.range n,a j x=_
   simp only [hk,a]; rw [add_comm]

theorem fitted {z ν:ℂ} (hR:0<R) (hz:z∈u)(h:AH u F) (n:ℕ)
    (ht:1 < ν.re+n) (hp:∀ j∈Finset.range n,ν+j≠0) : AnalyticAt ℂ (rent F R n z) ν:= by
   let V:={s:ℂ| 1 < (s+n).re}; have hx : IsOpen V:= isOpen_lt continuous_const (continuous_re.comp (continuous_add_const _))
   have hv : ν∈V:=by simpa [V] using ht
   have hk : AH V (fun p:ℂ×ℝ=>layer n (fun s=> F (z,s)) p.2):= AH.param_tame (layer_tame_ray n (h.slice hz))
   have hm(s:ℂ) (hs:s∈V): 0<(s+n-1).re:= by simpa [V] using hs
   unfold rent
   apply AnalyticAt.fun_add
   · exact (weight_ok hx hR.le (q:=fun s=> s+n-1) (fun _ _=> by fun_prop) hm hk).analytic hx hv 0
   apply Finset.analyticAt_fun_sum; intro j hj
   have hu : (R:ℂ)≠0:= ofReal_ne_zero.mpr hR.ne'
   exact ((Differentiable.analyticAt (f:=fun s:ℂ=>(R:ℂ)^(s+j)) (fun s=> (differentiableAt_id.add_const _).const_cpow (Or.inl hu)) ν).div ((analyticAt_id (𝕜:=ℂ)).add analyticAt_const) (hp j hj)).mul analyticAt_const

variable (h : AH neighborhood F) (hr : 0 < R)
include h hr

def age (n:ℕ)(z:ℂ):= -(n:ℂ)-2*z

def due (n:ℕ)(F:ℂ×ℝ→ℂ)(R:ℝ)(z:ℂ) := rent F R (n+2) z (age n z)

def walks : Filter ℂ := nhdsWithin 0 ({0}:Set ℂ)ᶜ
instance : walks.NeBot := by unfold walks; infer_instance

def Unfolds (A:ℂ→ℂ)(a:ℂ) := ∃ g:ℂ→ℂ, AnalyticAt ℂ g 0 ∧ A=ᶠ[walks] fun z => z⁻¹*a+g z

theorem due_open (n:ℕ): Unfolds (due n F R) (-(layer n (fun t=> F (0,t)) 0)/2) := by
   let f(j:ℕ)(z:ℂ) := (R:ℂ)^(age n z+j)*layer j (fun t=> F (z,t)) 0
   let k (j:ℕ) (z:ℂ) := f j z/(age n z+j)
   have hb(j:ℕ): AnalyticAt ℂ (fun z=> age n z+j) 0 := (differentiable_id.const_mul _|>.const_sub _|>.add_const _).analyticAt _
   have hR : (R:ℂ)≠0:= by exact_mod_cast hr.ne'
   have he(j:ℕ) : AnalyticAt ℂ (f j) 0 := by
      have hh := (peels_AH opened h j).analytic opened occurs 0
      have hv : Differentiable ℂ (fun z:ℂ=> (R:ℂ)^(age n z+j)):= fun z=>
         (((differentiableAt_id.const_mul _).const_sub _).add_const _).const_cpow (Or.inl hR)
      exact (hv.analyticAt _).mul hh
   have hf(j:ℕ)(hj : j≠n): AnalyticAt ℂ (k j) 0 := (he j).div (hb j) (by
      have hm: (j:ℂ)-(n:ℂ)≠0:= sub_ne_zero.mpr (by exact_mod_cast hj)
      simpa [age,add_comm,sub_eq_add_neg] using hm)
   let A := Finset.range (n+2)
   have hn : n∈A := Finset.mem_range.mpr (by omega)
   let d := fun z:ℂ=> dslope (f n) 0 z * (-1/2:ℂ)
   have hd : AnalyticAt ℂ d 0 := by
      obtain ⟨p,hp⟩:=he n; exact hp.has_fpower_series_dslope_fslope.analyticAt.mul analyticAt_const
   let F₀ (z:ℂ):= ∫ t in Ioc 0 R,(t:ℂ)^(age n z+↑(n+2)-1)*layer (n+2) (fun t=> F (z,t)) t
   have hF : AnalyticAt ℂ F₀ 0 := by
      let q(z:ℂ):= age n z+↑(n+2)-1
      apply (weight_ok opened hr.le (q:=q) ?_ ?_ (peels_AH opened h (n+2))).analytic opened occurs 0
      · intro z _; unfold q age; fun_prop
      intro z hz; have ht:= abs_re_le_norm z; have hw : ‖z‖<1/8:= by simpa [neighborhood] using hz
      unfold q age; simp; linarith [ht, le_abs_self z.re]
   refine ⟨fun z=> F₀ z+(∑ j∈ A.erase n,k j z)+d z, (hF.add (Finset.analyticAt_fun_sum _ (fun j hj=> hf j (Finset.ne_of_mem_erase hj)))).add hd,?_⟩
   filter_upwards [self_mem_nhdsWithin] with z hz
   have hrz : z ≠ 0 := hz
   unfold due rent
   have hp : ∀ j∈A,(R:ℂ)^(age n z+j)/(age n z+j)*layer j (fun t=> F (z,t)) 0 = k j z := fun j _=> by unfold k f; ring
   rw [Finset.sum_congr (s₁:=A) rfl hp,← Finset.sum_erase_add _ (fun j=> k j z) hn] -- function issue
   have hy : f n z=f n 0+z*dslope (f n) 0 z:= by
      have ht := sub_smul_dslope (f n) 0 z; simp at ht; linear_combination -ht
   have hj : age n z+n=-2*z:= by unfold age; ring
   have ho : f n 0=layer n (fun t=> F (0,t)) 0 := by simp [f,age]
   dsimp only [k,F₀,d]
   rw [hy,ho,hj]; field_simp; ring

end YM.SchemeConversionRG11.FirstMS.DR
