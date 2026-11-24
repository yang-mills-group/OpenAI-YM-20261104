import YM.MSbar.Pole.Feynman.Oath
/-! # Derivative flow passes to the projected value. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Set Filter MeasureTheory Ambient Momentum Age Mellin Piece Sew Thread Symbol PoleVal
open scoped Topology ContDiff BigOperators Classical Interval
variable {I : Type} [Fintype I]
namespace Soft
lemma handed {F:ℝ→ℂ→Cloud I}(h:Soft F)(n:ℕ)(x : External I n) {r:ℝ} (hr:0<r) {c:ℂ}
    (hx:Tendsto (fun z => deriv (fun i=> F i z n x) r) approaching (nhds c)) :
    HasDerivAt (fun s : ℝ=>pay (F s) n x) c r:= by
  obtain ⟨f,hf,H⟩:=h.discrete r hr n x
  let g(z:ℂ):ℂ:= fderiv ℝ f (r,z) (1,0)
  have hg : ContinuousAt g 0:= ((hf.continuousAt_fderiv (by simp)).clm_apply continuousAt_const).comp (continuousAt_const.prodMk continuousAt_id)
  have hh : ∀ᶠ z in approaching,∀ᶠ s in nhds r,F s z n x=f (s,z) := by
    have ht:=H; rw [nhds_prod_eq] at ht; obtain ⟨p,hp,q,hq,h⟩:=eventually_prod_iff.mp ht
    filter_upwards [hq.filter_mono (show approaching ≤ _ from nhdsWithin_le_nhds), self_mem_nhdsWithin (s:={(0:ℂ)}ᶜ)] with z hz ht; exact hp.mono fun _ hv=> h hv hz ht
  have h₁ : g 0=c:= by
    refine tendsto_nhds_unique_of_eventuallyEq (hg.continuousWithinAt) (show Tendsto _ (𝓝[≠] 0) _ from hx) ?_
    filter_upwards [hh,mem_nhdsWithin_of_mem_nhds (show ∀ᶠ z in nhds (0:ℂ), ContDiffAt ℝ 1 f (r,z) from (show ContinuousAt (fun z:ℂ=> (r,z)) 0 from continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds (hf.eventually (by simp)))] with z hz he
    exact ((show HasDerivAt (fun i:ℝ=>f (i,z)) (g z) r from (he.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt r ((hasDerivAt_id' _).prodMk (hasDerivAt_const ..))).congr_of_eventuallyEq hz |>.deriv).symm
  rw [← h₁]; refine (show HasDerivAt (fun t:ℝ=>f (t,0)) _ r from (hf.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt r ((hasDerivAt_id' _).prodMk (hasDerivAt_const ..))).congr_of_eventuallyEq ?_
  rw [nhds_prod_eq] at H; have he := H.curry
  have ht : ∀ᶠ s in nhds r, ContDiffAt ℝ 1 f (s,0) := (show ContinuousAt (fun s:ℝ=> (s,(0:ℂ))) r from continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds (hf.eventually (by simp))
  filter_upwards [he,ht,Ioi_mem_nhds hr] with s hp hb he
  refine tendsto_nhds_unique_of_eventuallyEq (ends (h.vortex s he) n x) ((show ContinuousAt (fun z:ℂ=> f (s,z)) 0 from hb.continuousAt.comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt) ?_
  filter_upwards [hp.filter_mono (show approaching ≤ _ from nhdsWithin_le_nhds), self_mem_nhdsWithin (s:={(0:ℂ)}ᶜ)] with z hz ht using hz ht
end Soft

namespace Feynman.Menu
variable [Nonempty I] {V:Type} {C : Menu I V} {D:District I V} (h:D.Clear C.chart)
    {μ s:ℝ} (hμ:0<μ) (hs:0<s) (n:ℕ) (x:External I n)
include h hμ hs
lemma block (hv:D.paths.Nonempty) :
    let J:=C.total μ D (C.run μ)
    HasDerivAt (fun r => C.connected μ D r n x) ((s:ℂ)⁻¹*pay (sum J C.chart.mom (D.weight C.chart) s) n x) s:= by
  intro J; let H:= (C.run μ D).ct; let X := C.chart.mom; let Y:= D.weight C.chart
  have ht: Accounts J X Y (D.view _) (D.opens _) H := sales C μ h hμ hv -- fix
  have ha : Flag J X Y (D.view _) (D.opens _):= aspired C μ h hμ fun _ h _=>done C μ h hμ
  have hh : Soft (C.primitive μ D):= unglazed (done C μ h hμ)
  let P(r:ℝ):= sum J X Y r; let Z:= pay (P s) n x; let K:= cooked J X Y; let T(r:ℝ):= sum K X Y r
  have hP(z:ℂ)(t:ℝ)(hp:0<t): C.primitive μ D t z n x= T t z n x - H z n x:= by
    have hw:(run C μ D).body=remit J X Y H:= by
      have hy:= means C μ hv; unfold H; rw [hy]
    unfold primitive; rw [hw,remit,sum_cons];
    change roll X ⟨Y,0⟩ t (-H) z n x+ T t z n x=T t z n x-H z n x
    rw [show roll X {a:=Y,l:=0} t (-H) z n x= -H z n x from (ht.charge z|>.neg).echo t hp z n x,neg_add_eq_sub]
  have hQ: ∀ᶠ z in approaching, deriv (fun i => C.primitive μ D i z n x) s=(s:ℂ)⁻¹* P s z n x:= by
    have hk (i:Fin J.length): ∀ᶠ z in approaching, let p:=J.get i
      HasDerivAt (fun i => roll X {a:=Y,l:=p.l} i (step X {a:=Y,l:=p.l} p.g) z n x) ((s:ℂ)⁻¹*roll X {a:=Y,l:=p.l} s p.g z n x) s := by
      let p:=J.get i; obtain ⟨⟨k,hk⟩,hl,hy⟩:=ha.law p (List.get_mem J i)
      exact Filter.Eventually.mono ((currents X {a:=Y,l:=p.l} hk hy).1) fun z hz=>hz n x s hs
    filter_upwards [eventually_all.mpr hk] with z hh
    let q(i:Fin J.length)(t:ℝ):=let p:= J.get i; roll X ⟨Y,p.l⟩ t (step X ⟨Y,p.l⟩ p.g) z n x
    have he : (fun t=>T t z n x)= fun t=>∑ i,q i t:=by funext; simp only [T,K,unifies,Finset.sum_apply]; rfl
    have hv : HasDerivAt (fun t=> T t z n x) ((s:ℂ)⁻¹ * P s z n x) s:= by
      unfold P; rw [he, unified]; simp_rw [Finset.sum_apply,Finset.mul_sum]; exact HasDerivAt.fun_sum fun i _=> hh i
    exact (((hv.sub_const _).congr_of_eventuallyEq (mem_of_superset (Ioi_mem_nhds hs) (fun i hi => hP z i hi))).deriv)
  have he : (fun z=>deriv (fun i => C.primitive μ D i z n x) s)=ᶠ[approaching] fun z=> (s:ℂ)⁻¹ * P s z n x := hQ
  refine Soft.handed hh n x hs (Tendsto.congr' (Filter.EventuallyEq.symm he) ?_)
  exact (ends (ha.clean s hs) n x).const_mul _
end Feynman.Menu
end YM.MSbar.Pole
