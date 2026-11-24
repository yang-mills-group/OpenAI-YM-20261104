import YM.RG11Proof.Jets.Law
/-!
# Power-log in the scale (inverse distance exp(u))

Exact engineering law on each evaluation/all u≥0, separately for each
fixed finite insertion/test/power demand, as in kpos/kcert on the FINAL
schemes (not intermediate Gram/position). Compact-scale bounds do not
suffice here; do not assert these for the actual raw regulator.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Scale
open scoped Classical BigOperators Topology
open PowerSeries Filter

/-- val evaluated on SINGLE scaled separated profile (or point configuration)
with shrinking distances `exp(-u)`, should scale with engineering weight w,
with a polynomial in u. Use real w to apply also with negative w in OPE.
On test arrays, convention is capture a Test under simultaneous scaling with
Jacobian cancelling position scale, no extra field rescalings absorbed. -/
def beam (w : ℝ) : Submodule ℝ (ℝ→ℝ) where
  carrier:={v | ∃ p:Polynomial ℝ, ∀ u : ℝ, 0≤u → v u=Real.exp (w*u) * p.eval u}
  zero_mem':= ⟨0, fun _ _=>by simp⟩
  add_mem':= by
    rintro v f ⟨p,h⟩ ⟨q,g⟩
    exact ⟨p+q, fun u he=> by simp [h u he,g u he,mul_add]⟩
  smul_mem':= by
    rintro c _ ⟨p,h⟩
    refine ⟨Polynomial.C c * p,fun u he=>?_⟩
    simp only [Pi.smul_apply, smul_eq_mul,h u he, Polynomial.eval_C_mul]; ring

theorem beamed {v:ℝ→ℝ} {w : ℝ}: v∈beam w ↔ ∃ p:Polynomial ℝ, ∀ u : ℝ, 0≤u → v u=Real.exp (w*u)*p.eval u:= Iff.rfl

/-- Below this engineering speed, beat even the logs. -/
def passes (w:ℝ): Submodule ℝ (ℝ→ℝ) where
   carrier:={v| Tendsto (fun u:ℝ=> Real.exp (-w*u) * v u) atTop (𝓝 0)}
   zero_mem':=by simp [tendsto_const_nhds_iff]
   add_mem':=by
     intro x y hx hy; change Tendsto _ _ _ at *
     simpa [mul_add] using hx.add hy
   smul_mem':=by
     intro z x hx; change Tendsto _ _ _ at *
     simpa only [Pi.smul_apply, smul_eq_mul,mul_zero, mul_left_comm z] using hx.const_mul z

theorem passed {v:ℝ→ℝ} {w:ℝ}: v∈passes w ↔ Tendsto (fun u : ℝ=>Real.exp (-w*u)*v u) atTop (𝓝 0):=Iff.rfl

theorem trail {v w : ℝ} (h:v<w) : beam v ≤ passes w:=by
  intro f hf
  obtain ⟨p,hp⟩ := beamed.mp hf
  refine passed.mpr ?_
  have he : Tendsto (fun u : ℝ=> p.eval u * Real.exp (-(w-v)*u)) atTop (𝓝 0):=by
    clear hp
    induction p using Polynomial.induction_on' with
    | monomial n c=>
      simpa only [Polynomial.eval_monomial, Real.rpow_natCast,mul_assoc,mul_zero] using
        (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero n (w-v) (sub_pos.mpr h)).const_mul c
    | add p q xp xq=>simpa only [Polynomial.eval_add,add_mul,zero_add] using xp.add xq
  apply he.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with u hu
  rw [hp u hu, ←mul_assoc, ← Real.exp_add]
  rw [show -w*u+v*u=-(w-v)*u by ring, mul_comm]

theorem negligible {f:ℝ→ℝ}{w:ℝ}(h:f∈beam w) (he: f∈ passes w) (u:ℝ)(hu:0≤u): f u=0:=by
  obtain ⟨p,hp⟩ := beamed.mp h
  have H : Tendsto (fun u=> p.eval u) atTop (𝓝 0):=by
    refine (passed.mp he).congr' ?_
    filter_upwards [eventually_ge_atTop (0:ℝ)] with a ha
    rw [hp a ha, ← mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, one_mul]
  rw [hp u hu,Polynomial.leadingCoeff_eq_zero.mp (p.tendsto_nhds_iff.mp H).1]; simp

end YM.RG11.Scale
