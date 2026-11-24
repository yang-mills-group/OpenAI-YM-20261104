import YM.Pert.Flow.Proxy
/-!
Transferring the one-loop slope to a coupling via finite jet comparison.
It requires (among other options) an o(g³) comparison, not just tangency.
-/
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1200000
namespace YM.Pert.Flow
open Function Filter Topology Extraction Asymptotics
open scoped Topology
variable {g y : ℝ→ℝ} {B u : ℝ}

structure Signature (b : ℝ) (g : ℝ → ℝ) : Prop where
    positive : ∀ᶠ t:ℝ in atTop,0 < g t
    concentration : Tendsto g atTop (𝓝 0)
    scale : Tendsto (fun t => g t * Real.sqrt t) atTop (𝓝 ((Real.sqrt (2*b))⁻¹))
    beta (u : ℝ) : 0 < u → Tendsto (fun t => (g (t+u)-g t)/(g t)^3) atTop (𝓝 (-b*u))

def Bent (g y : ℝ → ℝ) (a b : ℝ) (t : ℝ) : ℝ := (y t/g t-1-a*g t-b*(g t)^2)/(g t)^2

private lemma movePos {E : Type*} [TopologicalSpace E] {f : ℝ → E} {w:E} (h : Tendsto f atTop (𝓝 w)) (hu : 0 ≤ u) :
   Tendsto (fun t : ℝ => f (t+u)) atTop (𝓝 w) := h.comp (tendsto_atTop.2 fun k=> (eventually_ge_atTop k).mono (fun j hj=> show k ≤ j+u by linarith))

lemma signature_ratio (h : Signature B g) (hu: 0 < u) :
    Tendsto (fun t : ℝ => g (t+u)/g t) atTop (𝓝 1) := by
   have hh := tendsto_const_nhds (x:=(1:ℝ)) |>.add ((h.beta u hu).mul (h.concentration.pow 2))
   simp only [zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero] at hh
   apply hh.congr' (h.positive.mono fun t ht=> by
      change 1+(g (t+u)-g t)/(g t)^3*(g t)^2 = _
      field_simp; ring)

set_option linter.unusedTactic false in
private lemma shift_expansion (h : Signature B g) {a b : ℝ} (hy : Tendsto (Bent g y a b) atTop (𝓝 0)) (hu : 0 < u) :
   Tendsto (fun t => (y (t+u)-y t)/(g t)^3) atTop (𝓝 (-B*u)) := by
   let R:= Bent g y a b
   have hR := movePos (u:=u) hy hu.le
   have hg := movePos (u:=u) h.concentration hu.le
   have hz := h.concentration
   have hA := (tendsto_const_nhds (x:=(1:ℝ)) (f:=atTop (α:=ℝ))).add ((tendsto_const_nhds (x:=a)).mul
      (hg.add hz)) |>.add ((tendsto_const_nhds (x:=b)).mul ((hg.pow 2).add (hg.mul hz) |>.add (hz.pow 2)))
   simp only [mul_zero,zero_add,zero_pow (by decide : 2 ≠ 0),add_zero] at hA
   have h' := (h.beta u hu).mul hA |>.add (hR.mul ((signature_ratio h hu).pow 3)) |>.sub hy
   simp only [sub_zero,zero_mul,mul_one,add_zero] at h'
   obtain ⟨m,hm⟩ := eventually_atTop.mp h.positive
   have hEq {t : ℝ} (hg : 0<g t) : y t = g t + a*(g t)^2 + b*(g t)^3+R t*(g t)^3 := by
      dsimp [R,Bent]
      field_simp
      ring
   apply h'.congr' (eventually_atTop.mpr ⟨m,fun t ht=> by
      have he : m ≤ t+u := by linarith
      have hg:=hm _ ht; have hG:=hm _ he
      change (g (t+u)-g t)/(g t)^3*(1+a*(g (t+u)+g t)+b*((g (t+u))^2+g (t+u)*g t+(g t)^2))+R (t+u)*(g (t+u)/g t)^3-R t=_
      rw [hEq hG, hEq hg]; field_simp
      ring⟩)

theorem signedBend (h : Signature B g) {a b : ℝ} (hy : Tendsto (Bent g y a b) atTop (𝓝 0)) : Signature B y := by
   let K:= Bent g y a b
   have hD := h.concentration
   have hh := tendsto_const_nhds (x:=(1:ℝ)) |>.add ((tendsto_const_nhds (x:=a)).mul hD) |>.add
      ((tendsto_const_nhds (x:=b)).mul (hD.pow 2)) |>.add (hy.mul (hD.pow 2))
   simp only [mul_zero,add_zero,zero_mul,zero_pow (by decide : 2 ≠ 0)] at hh
   have hv : Tendsto (fun t => y t/g t) atTop (𝓝 1) := hh.congr' (h.positive.mono fun t ht=> by
      change 1+a*g t+b*(g t)^2+K t*(g t)^2 = y t/g t
      dsimp only [K,Bent];field_simp;ring)
   have hC : Tendsto y atTop (𝓝 0) := by
      have hx := hv.mul hD
      simp only [mul_zero] at hx
      exact hx.congr' (h.positive.mono fun t ht=>
         show y t/g t*g t=y t from div_mul_cancel₀ _ (ne_of_gt ht))
   refine ⟨?_,hC,?_,fun u hu=>?_⟩
   · exact (hv.eventually (lt_mem_nhds (show (0:ℝ)<1 from zero_lt_one))).and h.positive |>.mono fun t ht=> by
       have h : 0*(g t) < y t := (lt_div_iff₀ ht.2).1 ht.1
       simp only [zero_mul] at h; exact h
   · have hh := hv.mul h.scale
     rw [one_mul] at hh
     exact hh.congr' (h.positive.mono fun t ht=>
         by change y t/g t*(g t*_) = _; rw [← mul_assoc,div_mul_cancel₀ _ (ne_of_gt ht)])
   have hh := (shift_expansion h hy hu).mul ((hv.inv₀ one_ne_zero).pow 3)
   simp only [inv_one,one_pow,mul_one] at hh
   refine hh.congr' (h.positive.mono fun t ht=> ?_)
   change (y (t+u)-y t)/(g t)^3 * ((y t/g t)⁻¹)^3=_/(y t)^3
   rw [inv_div,div_pow]; field_simp

variable {G : Gauge} {C : Family G} {F : Order}
theorem proxySignature (hg : G.Simple) (P : Strain C F) : Signature (b0 G) (proxy P) :=
    ⟨proxy_positive P hg,proxy_zero P hg,proxy_asymptotic P hg,fun _=>proxy_running (G:=G) P hg⟩

end YM.Pert.Flow
