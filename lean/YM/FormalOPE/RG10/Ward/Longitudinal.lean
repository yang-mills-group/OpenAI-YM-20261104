import YM.FormalOPE.RG10.Ward.Ghosts

/-!
# Low-ghost-number BRST and identities on arbitrary multi-products at finite orbit

Use on our **ghost-free** Wilson prescription. In particular this says nothing about a Landau
regularization of the continuum BRST symmetry. `differential` is on degree (ghost number) ZERO
before imposing retained EOM identities separately on this sector. Koszul signs in this minimal
sector via genuine alternating cochains when evaluating ghosts. No multiplier 1/g in this convention
(raw unscaled link rule); convert links to their Taylor series EACH at their slot weight.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.InversionWard.BRST
open Gauge Lattice RG Wilson MeasureTheory Metric
open PertExtension PertExtension.Orb Function
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
open LieModule.Cohomology

variable {G : Gauge} {n : Side}

def chamber (G : Gauge) (n : Side) : Submodule ℝ (Config G n → ℝ) where
  carrier := {f | Proxy f}
  add_mem' := Proxy.add
  smul_mem' r _ h := h.const_smul r
  zero_mem' := Proxy.const 0

private lemma has_reply {f : Config G n → ℝ} (hf : Proxy f) (a : ghost G n) (U : Config G n) :
    HasDerivAt (fun t => f (curve a U t)) (response a f U) 0 := by
  obtain ⟨F,hF,rfl⟩:=hf
  rw [check a _ hF,Function.comp_apply]; exact (hF.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt_of_eq 0 (curve_deriv a U) (by rw [curve_zero])
lemma deriv_add {f g : Config G n → ℝ} (hf : Proxy f) (hg : Proxy g) (a : ghost G n) : response a (f+g) = response a f + response a g := by
  funext U; exact (has_reply (hf.add hg) a U).unique ((has_reply hf a U).add (has_reply hg a U))
lemma deriv_scale {f : Config G n → ℝ} (hf : Proxy f) (k : ℝ) (a : ghost G n) : response a (k • f) = k • response a f := by
  funext U; exact (has_reply (hf.const_smul k) a U).unique ((has_reply hf a U).const_mul k)
lemma deriv_plus {f : Config G n → ℝ} (hf : Proxy f) (a b : ghost G n) :
    response (a+b) f = response a f + response b f := by
  obtain ⟨F,h,rfl⟩:=hf; rw [check _ _ h, check _ _ h, check _ _ h]; funext x; dsimp only [Function.comp_apply, charge, Pi.add_apply]
  change fderiv ℝ F _ (spin (a+b) _) = _; rw [spin_add, map_add]; rfl
lemma scale_first {f : Config G n → ℝ} (hf : Proxy f) (a : ghost G n) (t : ℝ) : response (t • a) f=t • response a f := by
  obtain ⟨F,h,rfl⟩:=hf; rw [check _ _ h, check _ _ h]; funext x; dsimp only [Function.comp_apply, charge, Pi.smul_apply]; change fderiv ℝ F _ (spin (t • a) _) = _; rw [spin_smul, map_smul]; rfl
lemma gradedProduct {f g : Config G n → ℝ} (hf : Proxy f) (hg : Proxy g) (a : ghost G n) :
    response a (f*g) = response a f * g + f * response a g := by
  funext U; apply (has_reply (hf.mul hg) a U).unique; simpa [curve_zero] using (has_reply hf a U).fun_mul (has_reply hg a U)

noncomputable instance : LieRingModule (ghost G n) (chamber G n) where
  bracket a f := ⟨response a f.val, proxy_response a f.property⟩
  add_lie a b f := Subtype.ext (deriv_plus f.property a b)
  lie_add a f g := Subtype.ext (deriv_add f.property g.property a)
  leibniz_lie a b f := Subtype.ext (eq_add_of_sub_eq (commutator (G:=G) a b f.property))
noncomputable instance : LieModule ℝ (ghost G n) (chamber G n) where
  smul_lie t a f := Subtype.ext (scale_first f.property a t)
  lie_smul t a f := Subtype.ext (deriv_scale f.property t a)

/-- Zero to one. -/
def differential : chamber G n →ₗ[ℝ] oneCochain ℝ (ghost G n) (chamber G n) where
  toFun f := {
    toFun := fun a => ⁅a,f⁆
    map_add' _ _ := add_lie ..
    map_smul' _ _ := smul_lie .. }
  map_smul' k f := LinearMap.ext fun a => lie_smul k a f
  map_add' f g := LinearMap.ext fun a => lie_add a f g
lemma d0 (f : chamber G n) (a : ghost G n) : (differential f) a = ⁅a,f⁆ := rfl
lemma d0_read (f : chamber G n) (a : ghost G n) : ((differential f) a).val = response a f.val := rfl

/-- nilpotence from ghost degree zero. -/
lemma d1_d0 (f : chamber G n) : (d₁₂ ℝ (ghost G n) (chamber G n)) (differential f) = 0 := by
  apply Subtype.ext; ext a b : 2; change ⁅a,⁅b,f⁆⁆- ⁅b,⁅a,f⁆⁆- ⁅⁅a,b⁆,f⁆ = (0: chamber G n); rw [← lie_lie, sub_self]

/-- Symmetry under allowed gauge means BRST closed (even including disconnected components).
No converse or completeness/anomaly claims in this lemma. -/
theorem invariant (f : chamber G n) (h : respects f.val) : differential f = 0 := by
  ext a : 1; apply Subtype.ext; rw [d0_read];
  funext U; unfold response; rw [show (fun t => f.val (curve a U t))=(fun _=> f.val U) from funext fun k => h _ (chi_even a k) U]; exact deriv_const ..
end YM.FormalOPE.RG10.InversionWard.BRST
