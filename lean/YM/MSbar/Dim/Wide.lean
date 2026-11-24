import YM.MSbar.Dim.Plane

/-! Working throughout to sufficiently positive apparent number of dimensions (in pairs) for
analytic identities between contractions. Only these auxiliary Mellin identities; physical graph
loop integrals don't assume `d` large. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Dim
open Function Set Filter Metric Complex MeasureTheory Symbol
open scoped Topology ContDiff BigOperators Classical
variable {f g : ℂ→ℂ}
lemma wide (hf : ∀ z:ℂ,AnalyticAt ℂ f z) (hg :∀ z:ℂ,AnalyticAt ℂ g z) (r : ℝ)
   (h : ∀ z:ℂ,r<z.re→ f z=g z): f=g := by
    refine AnalyticOnNhd.eq_of_eventuallyEq (fun z _=>hf z) (fun z _=>hg z) (z₀:=↑(r+1)) ?_
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds (show (↑(r+1):ℂ)∈{z:ℂ|r<z.re} from lt_add_one r)] with z hz; exact h z hz

variable {K H : ℝ} {s z : ℂ} {F G: ℝ→ℂ}
lemma Radius.add (h : Radius H F) (hh : Radius H G) : Radius H (F+G):= ⟨h.size,h.smooth.add hh.smooth,fun r => by change F _+G _=_; rw [h.even,hh.even]; rfl,fun r hr=>by simp [h.ends _ hr,hh.ends _ hr]⟩
lemma Radius.zero (h : 0 ≤ H) : Radius H (0:ℝ→ℂ):= ⟨h,contDiff_const,fun _=>rfl,fun _ _=>rfl⟩
lemma emit_zero (z : ℂ) : radial 0 z=0:=by
    have hp:=Radius.zero (H:=1) zero_le_one
    refine congr_fun (wide (analytic hp) (fun _=>analyticAt_const (v:=(0:ℂ))) 0 (fun s hs=> ?_)) z; rw [actual hp hs]; simp [rootM,mellin]
lemma Radius.smul (h : Radius H F)(c:ℂ): Radius H (c • F) := ⟨h.size,h.smooth.const_smul c,fun r=> by simp [h.even _],fun r hr=> by simp [h.ends _ hr]⟩
lemma radial_add (hf : Radius H F) (hg : Radius K G) (z): radial (F+G) z=radial F z+radial G z:=by
   have hp:= (hf.thicken (le_max_left H K)).add (hg.thicken (le_max_right ..))
   refine congr_fun (wide (analytic hp) (fun z=>(analytic hf z).add (analytic hg z)) 0 (fun s hs=> ?_)) z
   change _=radial F _+radial G _; rw [actual hp hs,actual hf hs,actual hg hs,rootM,rootM,rootM]; simp_rw [Pi.add_apply]; rw [(hasMellin_add (rootM_diff hf hs).1 (rootM_diff hg hs).1).2,mul_add] -- name?
lemma radial_smul (h : Radius H F)(c z:ℂ) : radial (c • F) z=c*radial F z:=by
   have he:= h.smul c
   refine congr_fun (wide (analytic he) (fun z=>analyticAt_const.mul (analytic h z)) 0 ?_) z
   intro s hs; change _=c*radial F _; rw [actual he hs,actual h hs,rootM,rootM]; simp_rw [Pi.smul_apply]; rw [mellin_const_smul]; change _* (c* _)=_; ring
lemma radial_raised (h:Radius H F) (z:ℂ): radial F z=-(↑Real.pi:ℂ)⁻¹ * radial (raised F) (z+1):=by
   let g z:= -(↑Real.pi:ℂ)⁻¹ * radial (raised F) (z+1)
   refine congr_fun (wide (analytic h) (g:=g) (fun z=>analyticAt_const.mul ((analytic h.raising (z+1)).comp_of_eq (by fun_prop : AnalyticAt ℂ (fun t:ℂ=>t+1) z) rfl)) 0 ?_) z
   intro s hs; change _=-(↑Real.pi:ℂ)⁻¹ * _; rw [formula h (n:=1) (by simp; linarith),stage,actual h.raising (show 0<(s+1).re from (by simp; linarith))]; simp only [pow_one,Nat.cast_one,iterate_one,cpow_add (x:=↑Real.pi) s 1 (by exact_mod_cast Real.pi_ne_zero),cpow_one]
   have hp : (↑Real.pi:ℂ) ≠ 0:= by exact_mod_cast Real.pi_ne_zero
   field_simp <;> ring

-- scaling formula; useful for k>0.
lemma scale_radial (h : Radius H F) (a : ℝ) (ha : 0<a) (z : ℂ): radial (fun v=>F (a*v)) z=(↑(a^2):ℂ)^(-z)*radial F z:=by
   have hp:0<a^2:= by positivity
   have ht:Radius (H/a) (fun v=>F (a*v)):= by
        refine ⟨div_nonneg h.size ha.le,h.smooth.comp (by fun_prop),fun r=>by simp [h.even _],fun r hr=>?_⟩; rw [mul_comm]; exact h.ends _ ((div_lt_iff₀ ha).mp hr)
   have hA : Differentiable ℂ (fun z:ℂ=>(↑(a^2):ℂ)^(-z)):= fun z=> (differentiableAt_id (x:=z)).neg.const_cpow (Or.inl (by exact_mod_cast hp.ne'))
   refine congr_fun (wide (analytic ht) (fun z=>(hA.analyticAt z).mul (analytic h z)) 0 ?_) z
   intro s hs; rw [actual ht hs]; change _=_*radial F s; rw [actual h hs]; unfold rootM
   have he : (fun t=>F (a*Real.sqrt t))=fun t=> F (Real.sqrt (a^2*t)):=funext fun t=> by rw [Real.sqrt_mul hp.le,Real.sqrt_sq ha.le]
   rw [he,mellin_comp_mul_left (fun t=> F (Real.sqrt t)) _ hp]; change _ * (_ * _) = _; ring
end YM.MSbar.Dim
