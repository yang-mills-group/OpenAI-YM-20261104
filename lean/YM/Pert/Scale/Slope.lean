import YM.Pert.Scale.Measure
import YM.Pert.Scale.ControlInverse
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Scale
open Extra.FD Maxwell RawLabels Filter Set Topology Position Spec Climb Function
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {C : Family G} {I : Extraction.Order} {S : Table C.book} {n d : ℕ} {b : Final C I S} {X : Scaling S}
variable {Q : Conditions C.labels d n} {φ : Ledger Q → Buffer C.labels d} (h : FirstExtension b X) (hq : CleanProfiles Q) (hl : Reports (chart Q) (white Q) 0 φ)
include h hq hl
private lemma relDiff {s:ℝ} (hs:0<s) : ∀ᶠ k in atTop,∀ p, DifferentiableAt ℝ (fun t : ℝ=>relative X φ k t p) s := by
   obtain ⟨v,hv,w,hw,he⟩ := eventually_prod_iff.mp (clearance h hq hl hs)
   filter_upwards [hv,(correction_deriv h hq hl hs).1] with k hk hh p
   have hx := hh
   have heq : (fun t : ℝ=>relative X φ k t p) =ᶠ[𝓝 s] fun t=>choir C.labels (t,correction X φ k t) p := hw.mono (fun s hs=>rel_eq X (he hk hs).1 p)
   exact (((conducts C.labels p).differentiable (by decide)).differentiableAt.comp (f:=fun t=>(t,correction X φ k t)) s (differentiableAt_id.prodMk hx)).congr_of_eventuallyEq heq

/-- Infinitesimal frame transport in exact position scale coordinates, with inverse output. First term along windows about X.scales, not yet a rate in g. -/
theorem frame_log_step {s:ℝ} (hs:0<s) (p : E C.labels d) :
  Tendsto (fun k=> deriv (fun t:ℝ=>(positionScale X φ k s).symm (positionScale X φ k t p)) s) atTop
    (𝓝 ((gearIso C.labels d s hs).symm (deriv (fun t : ℝ=> gear C.labels d t p) s))) := by
  have he := relDiff h hq hl hs
  let M k := relative X φ k s
  let z k t := relative X φ k t p
  let D (k : ℕ) : E C.labels d →L[ℝ] E C.labels d :=
     (((M k).symm.toLinearMap).restrictScalars ℝ).toContinuousLinearMap
  have hf (k) {t : ℕ} (hk : DifferentiableAt ℝ (z k) s) :
     deriv (fun u:ℝ=>(positionScale X φ k s).symm (positionScale X φ k u p)) s= (M k).symm (deriv (z k) s) := by
    simp only [positionScale,LinearEquiv.symm_trans_apply,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]
    exact ((D k).hasFDerivAt.comp_hasDerivAt s (f:=z k) (DifferentiableAt.hasDerivAt (f:=z k) (𝕜:=ℝ) hk)).deriv
  have := control_inverse M (gearIso C.labels d s hs) (fun k => deriv (z k) s) (fun p=> (relative_leading h hq hl hs p).1) (relative_leading h hq hl hs p).2
  exact this.congr' (he.mono fun k hk=> (hf k (t:=0) (hk p)).symm)
omit h hq hl
open Extra.FD RawLabels Labels
lemma gear_prime (F : Frames G) {d : ℕ} (B : RStage F d) (s : ℝ) (i : Fin (B.m+1)) :
   HasDerivAt (fun t : ℝ=>gear F d t (B.b i)) (((B.w i).1 * (s:ℂ)^((B.w i).1-1)) • B.b i) s := by
     have ht (t:ℝ) : gear F d t (B.b i) = (t:ℂ)^_ • B.b i := rare B ..
     rw [funext ht,show ((B.w i).1:ℕ) * ((s:ℂ)^((B.w i).1-1))= ((B.w i).1:ℂ)*((s:ℂ)^((B.w i).1-1))* (1:ℂ) from (mul_one _).symm] -- type
     have h : HasDerivAt (fun x:ℝ=>(x:ℂ)) (1:ℂ) s := Complex.ofRealCLM.hasFDerivAt.hasDerivAt
     exact (h.pow _).smul_const (B.b i)
include h hq hl
theorem length_slope {s:ℝ} (hs:0<s) (i : Fin ((recorded C.labels d).m+1)) :
  let B := recorded C.labels d
  Tendsto (fun k=>s • deriv (fun t:ℝ=>(positionScale X φ k s).symm (positionScale X φ k t (B.b i))) s) atTop
    (𝓝 (((B.w i).1:ℕ) • B.b i)) := by
     intro B
     have ht := (frame_log_step h hq hl hs (B.b i)).const_smul s
     suffices he : s • ((gearIso C.labels d s hs).symm (deriv (fun t => gear C.labels d t (B.b i)) s)) = (B.w i).1 • B.b i by rwa [he] at ht
     apply (gearIso C.labels d s hs).injective
     rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) s,map_smul,LinearEquiv.apply_symm_apply]
     rw [(gear_prime C.labels B s i).deriv]
     rw [show (gearIso C.labels d s hs) ((B.w i).1 • B.b i)=gear C.labels d s ((B.w i).1 • B.b i) from rfl,← Nat.cast_smul_eq_nsmul ℂ,map_smul,rare,smul_smul,smul_smul]
     congr 1
     generalize (B.w i).1=v
     cases v with
     | zero => simpa
     | succ k =>
         rw [Nat.succ_sub_succ_eq_sub,Nat.sub_zero,pow_succ]
         change (s:ℂ) * (((k+1:ℕ):ℂ) * (s:ℂ)^k) = ((k+1:ℕ):ℂ) * ((s:ℂ)^k * (s:ℂ))
         exact Eq.trans (mul_left_comm ..) (congrArg _ (mul_comm _ _))
end YM.Pert.Scale
