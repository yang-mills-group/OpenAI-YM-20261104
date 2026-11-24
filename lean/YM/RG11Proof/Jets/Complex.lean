import YM.RG11Proof.Jets.Pencil
/-!
# Complex coefficient arrays and real frames

Recover complex coefficient identity at the SAME finite power horizon from
`realAt` plus profile phase. Don't truncate power after taking real/imag of a
product by complex coefficients; the proof uses precisely that the converting
frames and coupling have real coefficients. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Jets
open PowerSeries YM.PertExtension.Position
open scoped Classical BigOperators
local notation "cp"=>PowerSeries ℂ
local notation "rp"=>PowerSeries ℝ
/-- Deposit real FPS into complex coefficients. -/
def deposit : rp →+* cp := map Complex.ofRealHom
@[simp] theorem deposited (a : rp) (i:ℕ): coeff i (deposit a)=(↑((coeff i a):ℝ):ℂ):= rfl

def part (p : ℂ→ₗ[ℝ] ℝ) (a:cp) : rp:= PowerSeries.mk fun i=> p (coeff i a)

@[simp] theorem component (p:ℂ→ₗ[ℝ]ℝ) (a:cp) (i) : coeff i (part p a)=p (coeff i a):=by simp [part]

theorem part_line (p:ℂ→ₗ[ℝ]ℝ)(a:cp)(b:rp): part p (a * deposit b)=part p a*b:=by
  ext i
  simp only [component,coeff_mul, deposited,map_sum]
  apply Finset.sum_congr rfl; intro k _
  rw [mul_comm _ (↑(_ :ℝ):ℂ),← Complex.real_smul,map_smul,smul_eq_mul,mul_comm]

theorem part_total (p:ℂ→ₗ[ℝ]ℝ){I:Type*}(s:Finset I)(a:I→cp): part p (∑ i∈s,a i)=∑ i∈s,part p (a i):=by ext i; simp_rw [component,map_sum,component]

theorem deposit_base (c:rp)(h:Anchored c): Anchored (deposit c):=by unfold Anchored; rw [←coeff_zero_eq_constantCoeff_apply,deposited,coeff_zero_eq_constantCoeff_apply,h,Complex.ofReal_zero]

theorem part_comp (p:ℂ→ₗ[ℝ]ℝ) (a:cp) (b:rp)(hb: Anchored b): part p (PowerSeries.subst (deposit b) a) = PowerSeries.subst b (part p a):=by
   ext i; simp_rw [component,coeff_compose _ _ _ (deposit_base b hb),coeff_compose _ _ _ hb,component,map_sum,←map_pow deposit,deposited]
   exact Finset.sum_congr rfl fun k _=> by rw [mul_comm _ (↑(_ :ℝ):ℂ),←Complex.real_smul,map_smul,smul_eq_mul,mul_comm]

variable {J P : Type*} [Fintype J] {d:P→ℕ}
def toComplex (p:Change ℝ J):Change ℂ J:=⟨deposit p.g,p.Z.map deposit⟩

theorem part_transform (a:ℂ→ₗ[ℝ]ℝ)(A:ArrayAt J ℂ d)(c:Change ℝ J)(h:Anchored c.g)(v:Mark J d):
    c.act (fun w=>part a (A w)) v = part a ((toComplex c).act A v):=by
  unfold Change.act PertExtension.Position.insert
  rw [part_total]; apply Finset.sum_congr rfl; intro w _
  unfold toComplex; simp only [Matrix.map_apply,←map_prod deposit,part_line,part_comp _ _ _ h]

abbrev real : ℂ →ₗ[ℝ] ℝ := Complex.reCLM.toLinearMap
abbrev imag : ℂ →ₗ[ℝ] ℝ := Complex.imCLM.toLinearMap

theorem split_parts {A B:cp}(hr:part real A=part real B)(hi:part imag A=part imag B): A=B:=by
  ext1 k
  apply Complex.ext
  · exact Eq.trans (component real A k).symm ((congrArg (coeff k) hr).trans (component real B k))
  exact Eq.trans (component imag A k).symm ((congrArg (coeff k) hi).trans (component imag B k))

-- It suffices that there is a profile twist capturing imag by another real
-- price at same labels and arity. Here split re and im on arbitrary Mark,
-- version with twist in Fields below (uses this identity). Finite power form.
theorem complex_derives {A B : ArrayAt J ℂ d} (c : Change ℝ J) (hc : Anchored c.g) {n}
   (hr : ∀ v, Through n (part real (A v)) (c.act (fun i=>part real (B i)) v))
   (hi : ∀ v, Through n (part imag (A v)) (c.act (fun i=>part imag (B i)) v)) (v) :
   Through n (A v) ((toComplex c).act B v):= by
  intro l hl
  apply Complex.ext
  · have h:= hr v l hl; rw [part_transform _ _ _ hc] at h
    change real _=real _
    simpa only [component] using h
  have h:=hi v l hl; rw [part_transform _ _ _ hc] at h
  exact show imag _=imag _ from (by simpa only [component] using h)
end YM.RG11.Jets
