import YM.QuadraticLocal.Earn.Invoice
/-! # Weighted version of Invoice.paying, for residual on THESE rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn
open Function Filter Finset Lattice RG Wilson Marker Ac Gauge
open Push Push.AbsoluteSums Paths Animals
open AnalyticBridge VerifiedReset Collection Precision Exterior Extra.Iteration Next.Scheduling Next.Foundations
open QuadraticLocal.Sunrise
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V α ι : Type*}[DecidableEq V]{G:Gauge}{n:Side}
variable {P:Passport n V} {R:Census V} {g a e σ r b :ℝ}
namespace Invoice
open Row Wages
variable (B:BudgetPoint)(U:ℝ)
variable (X:ι→ Row P R G α)(t:V→ℝ) (hw:∀ i,0<t i)
-- common growth for current Epoch.Both projected height α.T.Global taxes.Title ≤ aν etc. need positivity on V.Boost.
local notation "M"=> B.B
local notation "Zoo"=> B.power*B.order

variable (s Ψ:ℕ)
local notation "fee"=> (Invoice.liberty G (B.power*B.order) s B.power B.order B.B U)
variable (hU:Supports B U a g σ e)
variable (hℓ:Offers X t σ r) (h₁: ∀ i,(X i).Graceful σ)(hJ:∀ i,(X i).lamp.r ≤ s) (hq:∀ i,(X i).mode.val.card ≤ Ψ)
variable (f:ι→ℝ) (v:ℝ) (hv:0 ≤ v)
variable (hf:∀ i,|f i| *g^(X i).lamp.e ≤ v)
include hf hv hw hU hℓ h₁ hJ hq
lemma taxes (m:ℕ) (x:Site n) : SumBudget (fun i=> if m ≤ (X i).length then if x∈(X i).ground B then (|f i| *income B X t g i)*Real.exp (a*(coverNumber B.B ((X i).ground B):ℝ)) else 0 else 0) (v*price B U s Ψ a e G * r * Real.exp (-e)^m):=by
    obtain ⟨hg,hg',hU',ht,hσ,hT⟩:= hU
    let φ i:=Poly.toll t (X i).mode * (X i).salary; let z i:=(X i).center; let l i:=(X i).length; let X0 i:=(X i).ground B; let F i:=(X i).height σ
    let p:=(B.power*B.order+memories B s)
    have hφ i:0<φ i:=mul_pos (Poly.worth hw _) ((X i).sound)
    have hz : Footprint.Anchored z φ l σ r:= by
       intro i; convert hℓ i using 1; ext j; unfold φ; split
       next h=>unfold Row.height l; ring
       next=>rfl
    have hΦ(i): |f i| *income B X t g i ≤ v*fee*φ i*(1+(l i:ℝ))^p:= by
       have he: g^(X i).lamp.e ≤ (1:ℝ):= pow_le_one₀ hg.le hg'
       let a₁:=(1+(l i:ℝ))^p
       have hh:= letters (a:=a) (g:=g) (e:=e) B U s (X i) ⟨hg,hg',hU',ht,hσ,hT⟩ (h₁ i) (hJ i)
       change _ ≤ g^(X i).lamp.e * fee * a₁ at hh
       rw [show income B X t g i=(X i).baseCost B g * φ i from (by unfold income φ Row.charge; ring)];
       have hs:0≤ fee:= (pay_nn U s hU' G Zoo B.order B.power B.B).le; have hj:0≤ a₁:=by unfold a₁; positivity
       rw [ ←mul_assoc]; apply (mul_le_mul_of_nonneg_right _ (hφ i).le).trans_eq (b:=v*fee*a₁*φ i) (mul_right_comm ..);
       apply (mul_le_mul_of_nonneg_left hh (abs_nonneg (f i))).trans; rw [ ←mul_assoc,←mul_assoc ]; gcongr; exact hf i
    let hL : Supports B U a g σ e:= ⟨hg,hg',hU',ht,hσ,hT⟩; have he := Footprint.assigned_tail (id : Site n→Site n) 1 (fun i=>by simp) z φ (fun i=>(hφ i).le) l X0 hz (B.B+2) p B.B (fun i j hj=>?_) (fun i=>?_) (mul_nonneg hv (pay_nn U s hU' G Zoo B.order B.power B.B).le) hT (fun i=> |f i| *income B X t g i) (fun i=> mul_nonneg (abs_nonneg _) (income_nn B X t g i hw)) hΦ m x («v»:=Invoice.tax s Ψ) -- find infer
    rotate_left
    · rw [id_eq, separation_comm]; have h:=near (X i) _ j hj; exact h.trans (by unfold Row.radius l; nlinarith)
    · let i0:=X i; have hr:0< (M:ℝ):=Nat.cast_pos.mpr B.B_pos; have hh : M * coverNumber M (X0 i) ≤ (1000+s+Ψ)*M+l i:= (i0.tiles M B.B_pos).trans (by unfold i0; gcongr <;> first | apply hJ | apply hq)
      unfold tax; field_simp; push_cast; rw [Nat.mul_comm M] at hh; exact_mod_cast hh
    exact budget_loosen he (le_of_eq (by unfold price Footprint.payment Footprint.degreeIncome; ring))
end Invoice
end YM.QuadraticLocal.Earn
