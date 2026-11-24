import YM.Pert.Asymptotics.RawAxis
/-!
# Short-step kinetic slope on the actual Wilson trajectory

From the construction receipt alone, this is *only* a law for the effective
inverse coefficient in `C.path.rep N p m`, taking both readings along the
same RG trajectory. It is not the position coupling of the continuum correlators.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Pert.Flow
open Function Filter Topology RG Asymptotics
open scoped Topology
variable {G : Gauge} {C : Family G} {N p : ℕ → ℕ}

def logStride (C : Family G) (m : ℕ) := Real.log ((C.S.block m).val:ℝ)
lemma stride_pos (i) : 0 < logStride C i := Real.log_pos (by exact_mod_cast (show 1 < (C.S.block i).val by
   exact Nat.lt_of_lt_of_le (by decide) (C.S.block_large i)))
lemma drift_price : Tendsto (fun m=> (C.path.levels.params (m+1)).drift/logStride C m) atTop (𝓝 0) := by
   let c := C.path.levels.clock
   have hs := (show StrictMono (fun i:ℕ=>i+1) from fun _ _ hij=>Nat.add_lt_add_right hij 1).tendsto_atTop
   have hg := tendsto_natCast_atTop_atTop (R:=ℝ) |>.comp (C.path.levels.fits.deep.comp hs)
   have hq := tendsto_pow_atTop (α:=ℝ) (n:=2) (by decide)
   have hi : Tendsto (fun m:ℕ => ((c.J (m+1) : ℝ)^2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (hq.comp hg)
   exact Filter.Tendsto.squeeze tendsto_const_nhds hi
      (fun m=> div_nonneg (C.path.levels.params (m+1)).drift_ge ((stride_pos m).le))
      (fun m=> C.path.levels.fits.driftSmall m)

variable (hc : C.Makes) (hh : ∀ᶠ i : ℕ in atTop, i<N i)
include hc hh

theorem raw_step_slope :
   Tendsto (fun i : ℕ => (C.path.β (N i) (p i) (i+1)-C.path.β (N i) (p i) i)/logStride C i)
      atTop (𝓝 (2*b0 G)) := by
   refine Metric.tendsto_nhds.2 (fun ε h=> ?_)
   filter_upwards [drift_price (C:=C)|>.eventually (gt_mem_nhds h),hh] with m hC hN
   have hs:= (hc.wilson.steps (N m) (p m) m hN).2
   have hsid:=stride_pos (C:=C) m
   rw [Real.dist_eq,
      show ((C.path.β (N m) (p m) (m+1) - C.path.β (N m) (p m) m)/logStride C m-2*b0 G) =
        (C.path.β (N m) (p m) (m+1) - C.path.β (N m) (p m) m-G.slopeConstant * logStride C m)/logStride C m from by
          rw [b0_normalizes]; field_simp,abs_div,abs_of_pos hsid]
   exact (div_le_div_of_nonneg_right hs hsid.le).trans_lt hC

omit hc hh in
private lemma margin (G : Gauge) (hg : G.Simple) : 0<2*b0 G := Asymptotics.b0_normalizes (G:=G) ▸ Gauge.slopeConstant_pos hg
variable (hg : G.Simple)
include hg

lemma raw_level_ratio :
   Tendsto (fun i : ℕ => C.path.β (N i) (p i) (i+1)/C.path.β (N i) (p i) i) atTop (𝓝 (1:ℝ)) := by
   let b i := C.path.β (N i) (p i) i
   have hi : Tendsto (fun i=>b i/C.S.scale i) atTop (𝓝 (2*b0 G)) :=
      Metric.tendsto_nhds.2 (fun ε h=>by
         filter_upwards [zeroUp_bound C hc h,hh] with k H hk
         rw [Real.dist_eq]
         exact H _ _ hk.le)
   have he : Tendsto (fun i=>logStride C i/C.S.scale i) atTop (𝓝 0):= C.path.levels.fits.mesh
   have hf := he.div hi (margin G hg).ne'
   rw [zero_div] at hf
   have hA : Tendsto (fun i=>logStride C i / b i) atTop (𝓝 0) := hf.congr'
      ((C.S.divergent.eventually_gt_atTop 0).mono fun i hi=> by
         change (logStride C i / C.S.scale i) / (b i / C.S.scale i) = _
         field_simp)
   have hv := (raw_step_slope hc hh (p:=p)).mul hA
   rw [mul_zero] at hv
   have hy := (tendsto_const_nhds (x:=(1:ℝ))).add hv
   rw [add_zero] at hy
   refine hy.congr' ((hh.and ((C.S.divergent.eventually_gt_atTop 0).and (hi.eventually (lt_mem_nhds (margin _ hg))))).mono fun i hr=> ?_)
   have hpos : b i/C.S.scale i>0 := hr.2.2
   have hb: 0 < b i := (div_pos_iff.mp hpos).resolve_right (fun h=> not_lt_of_ge hr.2.1.le h.2) |>.1
   have hl : logStride C i ≠0 := (stride_pos (C:=C) i).ne'
   change 1+(C.path.β _ _ _-b i)/_ * (_/b i)=_
   dsimp [b] at *
   field_simp <;> try ring

theorem raw_beta_lead :
   Tendsto (fun i =>
      let g:= regulatorRun C (N i) (p i)
      ((g (i+1)-g i)/(g i)^3) / logStride C i) atTop (𝓝 (-b0 G)) := by
   have hb := raw_level_ratio hc hh (p:=p) hg
   have hs := Real.continuous_sqrt.continuousAt (x:=(1:ℝ)) |>.tendsto.comp hb
   rw [Real.sqrt_one] at hs
   have h := (raw_step_slope hc hh (p:=p)).neg
   have hy := h.div (hb.add hs) (show (1:ℝ)+1≠0 from by norm_num)
   rw [show -(2*b0 G) / (1+1) = -b0 G from by ring] at hy
   refine hy.congr' (hh.mono ?_)
   intro i hv
   have h₁:= (hc.wilson.represents _ (p i) _ hv.le).band.1
   have h₂:= (hc.wilson.represents _ (p i) _ hv).band.1
   have hsid:= (stride_pos (C:=C) i).ne'
   let b:= C.path.β (N i) (p i) i
   let B:= C.path.β (N i) (p i) (i+1)
   have hb : 0<b := lt_of_lt_of_le (half_pos (lt_trans zero_lt_one (C.path.levels.fits.delayed _))) h₁
   have hB : 0<B := lt_of_lt_of_le (half_pos (lt_trans zero_lt_one (C.path.levels.fits.delayed _))) h₂
   let s:=Real.sqrt b;let t:=Real.sqrt B
   have hz:s^2=b:= Real.sq_sqrt hb.le
   have ht:t^2=B:= Real.sq_sqrt hB.le
   have hp:s>0:= Real.sqrt_pos.2 hb; have hq:t>0:= Real.sqrt_pos.2 hB
   change (- ((B-b)/logStride C i))/(B/b+Real.sqrt (B/b)) =
      ((t⁻¹-s⁻¹)/(s⁻¹)^3)/_
   rw [Real.sqrt_div hB.le];change - _/(B/b+t/s) = _
   have hst : B/b+t/s≠0:=by positivity
   field_simp <;> try ring
   rw [←hz,←ht]
   ring

end YM.Pert.Flow
