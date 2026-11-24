import YM.MSbar.Symbol.Average
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Radial derivative for normalized dimensional continuation

`raised f` differentiates in the squared radius. **Not** undefined/singular at zero: for even
smooth f it's again even smooth f. Treat the continuation dimension as the complex number of PAIRS
of real dimensions. Insertion and momentum tensors keep full O(2m) real convention, not only unitary
transforms on those pairs. This module can be parameter-uniform.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Dim
open Function MeasureTheory Filter Set
open scoped Topology ContDiff BigOperators Classical

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

-- integrated twice derivative in ordinary radius
-- use Icc always including zero endpoints
def raised (f : ℝ → E) (r : ℝ) := ∫ t in Icc (0:ℝ) 1, (1/2 : ℝ) • (deriv (deriv f) (t*r))
omit [CompleteSpace E] in
lemma twice_even {f : ℝ → E} (hp : Function.Even f) (r : ℝ) : deriv (deriv f) (-r) = deriv (deriv f) r := by
   have he : (fun t:ℝ=> f (-t))=f:= funext hp
   have h(r:ℝ): deriv f r= -deriv f (-r):= by
      calc _ = deriv (fun t:ℝ=> f (-t)) r := by rw [he]
           _ = _ := deriv_comp_neg _ _
   have he': (fun t:ℝ=> deriv f (-t))=fun t=> -deriv f t := funext fun r => by simpa using h (-r)
   apply neg_injective
   rw [← deriv_comp_neg]; rw [he']; simp

omit [CompleteSpace E] in
lemma raised_even {f : ℝ → E} (he : Function.Even f) : Function.Even (raised f) := fun x => by simp_rw [raised,mul_neg,twice_even he]

lemma raised_id {f : ℝ → E} (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (r : ℝ) :
    (2*r) • raised f r=deriv f r := by
    have h0 : deriv f 0=0:= by
        have ht : deriv f 0 = -deriv f (-0) := by
          rw [← deriv_comp_neg]; rw [funext he]
        have h2 : (2:ℝ) • deriv f 0=0:= by
          rw [two_smul ℝ]; simp at ht -- hm
          exact eq_neg_iff_add_eq_zero.mp ht
        exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
    let u (t:ℝ):= t*r
    have hd := (contDiff_infty_iff_deriv.mp hf).2
    let F(t:ℝ):= deriv f (u t)
    have H(x): HasDerivAt F (r • (deriv (deriv f) (u x))) x:=by
       let v:= (hd.differentiable (by simp) (u x)).hasDerivAt
       have hu : HasDerivAt u r x:= by unfold u; simpa using (hasDerivAt_id' x).mul_const r
       exact v.scomp x hu
    have hI: Continuous (fun t : ℝ=> r • deriv (deriv f) (u t)):= ((contDiff_infty_iff_deriv.mp hd).2.continuous.comp (by unfold u; fun_prop : Continuous u)).const_smul _
    calc (2*r) • raised f r= ∫ t in Icc (0:ℝ) 1,r • deriv (deriv f) (u t) := by
            unfold raised; rw [← integral_smul]; simp_rw [smul_smul,show 2*r*(1/2)=r by ring]; rfl
         _ = ∫ t in (0:ℝ)..1,r • deriv (deriv f) (u t) := by rw [intervalIntegral.integral_of_le (zero_le_one),integral_Icc_eq_integral_Ioc]
         _ = F 1-F 0:=intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _=> H x) (hI.intervalIntegrable ..)
         _ = _:= by simp [F,h0,u]

-- under finite-dimensional parameters
omit [CompleteSpace E] [FiniteDimensional ℝ X] in
@[fun_prop] lemma radial_slope {F : X × ℝ → E} (hf : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (fun p : X × ℝ=> deriv (fun t=> F (p.1,t)) p.2):= by
   have he : (fun p : X × ℝ=> deriv (fun t=> F (p.1,t)) p.2)= fun p=> fderiv ℝ F p (0,1):= by
      ext1 p
      have h := (hf.differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt p.2 ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)) -- arg infer
      exact h.deriv
   rw [he]; exact (ContinuousLinearMap.apply ℝ E ((0,1):X × ℝ)).contDiff.comp (hf.fderiv_right (by simp))
omit [CompleteSpace E] [FiniteDimensional ℝ X] in
@[fun_prop] lemma radial_tame {F : X × ℝ → E} (hf : F.HasTemperateGrowth) : (fun p : X × ℝ=> deriv (fun t=> F (p.1,t)) p.2).HasTemperateGrowth:= by
   have he : (fun p : X × ℝ=> deriv (fun t=> F (p.1,t)) p.2)= fun p=> fderiv ℝ F p (0,1):= by
      ext1 p
      have h := (hf.1.differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt p.2 ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)) -- arg infer
      exact h.deriv
   rw [he];exact (ContinuousLinearMap.apply ℝ E ((0,1):X × ℝ)).hasTemperateGrowth.comp (Symbol.tame_fderiv hf)

lemma raised_joint {F : X × ℝ → E} (hf : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (fun p : X × ℝ=> raised (fun t=> F (p.1,t)) p.2):=by
   let μ:= volume.restrict (Icc (0:ℝ) 1); haveI : IsFiniteMeasure μ:= by unfold μ; infer_instance
   let P (p:X × ℝ):= deriv (fun t=> deriv (fun u=> F (p.1,u)) t) p.2
   have hp : ContDiff ℝ ∞ P := radial_slope (radial_slope hf)
   let g : (X × ℝ) × ℝ → X × ℝ:= fun p=> (p.1.1,p.2*p.1.2)
   refine Symbol.average_smooth (ContinuousLinearMap.lsmul ℝ ℝ) aestronglyMeasurable_id (ae_restrict_mem (s:=Icc (0:ℝ) 1) measurableSet_Icc) isCompact_Icc (μ:=μ) (integrable_const (1/2:ℝ)) (hp.comp (by unfold g; fun_prop : ContDiff ℝ ∞ g))

lemma raised_tame {F : X × ℝ → E} (hf : F.HasTemperateGrowth) : (fun p : X × ℝ=> raised (fun t=> F (p.1,t)) p.2).HasTemperateGrowth:=by
   let μ:= volume.restrict (Icc (0:ℝ) 1); haveI : IsFiniteMeasure μ:= by unfold μ; infer_instance
   let P (p:X × ℝ):= deriv (fun t=> deriv (fun u=> F (p.1,u)) t) p.2
   have hp : P.HasTemperateGrowth := radial_tame (radial_tame hf)
   let g : (X × ℝ) × ℝ → X × ℝ:= fun p=> (p.1.1,p.2*p.1.2)
   let f := ContinuousLinearMap.fst ℝ (X × ℝ) ℝ
   let d := ((ContinuousLinearMap.fst ℝ X ℝ).comp f)
   let r := ((ContinuousLinearMap.snd ℝ X ℝ).comp f)
   have hT := ((ContinuousLinearMap.snd ℝ (X × ℝ) ℝ).hasTemperateGrowth.mul r.hasTemperateGrowth)
   let ι:= ContinuousLinearMap.inl ℝ X ℝ
   let j:= ContinuousLinearMap.inr ℝ X ℝ
   have h : g = (fun x=>ι (d x)) + (⇑j ∘ (fun p=>(ContinuousLinearMap.snd ℝ (X × ℝ) ℝ p)*r p)):= by
       funext p; change (p.1.1,p.2*p.1.2)= (p.1.1,0)+(0,p.2*p.1.2)
       simp
   have hx : HasTemperateGrowth g:= h ▸ (ι.hasTemperateGrowth.comp d.hasTemperateGrowth).add (j.hasTemperateGrowth.comp hT)
   refine Symbol.average_growth (ContinuousLinearMap.lsmul ℝ ℝ) aestronglyMeasurable_id (ae_restrict_mem (s:=Icc (0:ℝ) 1) measurableSet_Icc) isCompact_Icc (μ:=μ) (integrable_const (1/2:ℝ)) (hp.comp hx)

lemma raised_smooth {f : ℝ→E} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (raised f) :=by
   let F:= f ∘ (Prod.snd : ℝ × ℝ→ℝ)
   have hp : ContDiff ℝ ∞ F:= hf.comp contDiff_snd
   exact (raised_joint hp).comp (contDiff_id.prodMk contDiff_id)

lemma raised_zero_of {f : ℝ→E} (hf : ContDiff ℝ ∞ f) (he : Function.Even f) {r : ℝ} (h : r ≠ 0) (hw : f =ᶠ[𝓝 r] fun _=>0) : raised f r=0:=by
   refine (smul_eq_zero.mp (?_ : (2*r) • raised f r=0)).resolve_left (by simp [h])
   rw [raised_id hf he]; simpa using hw.deriv_eq

structure Radius (H : ℝ) (f : ℝ→E) : Prop where
   size : 0 ≤ H
   smooth : ContDiff ℝ ∞ f
   even : Function.Even f
   ends : ∀ r : ℝ,H<r→f r=0
variable {f : ℝ→E} {H : ℝ}

lemma Radius.raising (h : Radius H f) : Radius H (raised f) :=by
    obtain ⟨hp,ht,he,h⟩:=h
    refine ⟨hp,raised_smooth ht,raised_even he,fun r hr=> raised_zero_of ht he (hp.trans_lt hr).ne' ?_⟩
    filter_upwards [lt_mem_nhds hr] with y hy; exact h y hy
lemma Radius.repeat (h : Radius H f) (n : ℕ) : Radius H (raised^[n] f):= Nat.rec h (fun i ih=> iterate_succ_apply' .. ▸ ih.raising) n
lemma Radius.thicken (h : Radius H f) {A : ℝ} (hA : H ≤ A) : Radius A f := ⟨h.size.trans hA,h.smooth,h.even,fun r hr=>h.ends r (hA.trans_lt hr)⟩

-- compatibility under addition, maps etc.
lemma raised_map {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E'] (L : E →L[ℝ] E') (hf : ContDiff ℝ ∞ f) : raised (L ∘ f)=L ∘ raised f := by
    have ht := (contDiff_infty_iff_deriv.mp hf).2; have hu := (contDiff_infty_iff_deriv.mp ht).2
    have he : ∀ (g : ℝ→E), ContDiff ℝ ∞ g → deriv (L ∘ g)= L ∘ deriv g := by
       intro g hg; funext x; exact (L.hasFDerivAt.comp_hasDerivAt x ((hg.differentiable (by simp) x).hasDerivAt)).deriv
    funext r; simp_rw [raised,he f hf, he (deriv f) ht, comp_apply,← map_smul]
    exact L.integral_comp_comm (by apply Continuous.continuousOn _ |>.integrableOn_compact isCompact_Icc; exact (hu.continuous.comp (by fun_prop)).const_smul _)

lemma raised_add {g : ℝ→E} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) : raised (f+g)=raised f+raised g := by
    let h : ℝ → E × E:= fun x => (f x,g x)
    let i:= ContinuousLinearMap.fst ℝ E E; let j:=ContinuousLinearMap.snd ℝ E E
    have H := hf.prodMk hg; change ContDiff ℝ ∞ h at H
    have he : f+g=(i+j : E × E→L[ℝ] E) ∘ h := rfl
    funext x; rw [he]; exact (congr_fun (raised_map (i+j) H) x).trans (Eq.symm (congr_arg₂ (·+·) (congr_fun (raised_map i H) x) (congr_fun (raised_map j H) x)))
end YM.MSbar.Dim
