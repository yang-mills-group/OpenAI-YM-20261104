import YM.AllOrder.Iron.Stamp
import YM.Next.STATIONARY.Joint.FourPoint
import YM.Next.STATIONARY.Joint.HaarJac
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Iron
open Lattice Laurent RG Filter Tree Metric Finset Function Gauge Matrix Module
open Exterior Wilson Precision Tree MeasureTheory Stationary
open scoped Matrix BigOperators Topology Classical ContDiff InnerProductSpace Matrix.Norms.Frobenius ENNReal
variable {G:Gauge}{c f:Side}{S:StepData c f} (F:Forest S.ratio)(t:S.Choices) {p:Clip}{R:PathData G}

lemma shell_bound (h: Shell S t p R (1:Config G c) (1:Joint G c f)) :
    let P:= rangers F G; let H:= damage (helmets G c f) (canon S t p R 1 1) 0; hessian F t p R 0 0=Pᵀ*H*P:=by
    intro P H; let x: Bid.Dir G c:=0
    have hh : (represent x:Config G c)=1:= by simp [x] -- name
    let L : AxisChart G F →L[ℝ] Vault G c f:=(pad F).prod 0
    let Q := canon S t p R (1:Config G c) (1:Joint G c f)
    have he : saver F (0:AxisChart G F)=ᶠ[𝓝 0] id := by
       refine Eventually.mono (p:=fun b=>∀ i:F.Free,saver F (0:AxisChart G F) b i=b i) (eventually_all.mpr fun i=> ?_) (fun _ h=>funext h)
       have ht : Tendsto (fun b:AxisChart G F=> b i) (𝓝 0) (𝓝 0):= (continuous_apply ..).continuousAt
       filter_upwards [ht.eventually G.plog_left] with d hd; simpa only [saver,buck,plogC,Pi.zero_apply,G.mat_lieExp_zero,inv_one,mul_one] using hd
    have he' : tested F t p R x=ᶠ[𝓝 0] Q ∘ L := by
       filter_upwards [saving x (0:AxisChart G F),he] with b hb hp; rw [← merit_pin, hh]; rw [hh,abode_zero, hp] at hb; change _=muster S t p R 1 _; exact congr_arg (muster S t p R 1) hb.symm
    rw [show hessian F t p R 0 0=damage _ _ _ from Work.F05.hessian_eq ..,damage_congr _ he']
    exact damage_rate _ _ _ _ h.1

section
local notation "M"=> medals S t p R
lemma sheer (n m f : Funds (Bodies G c f)) (h:n=fᵀ*m*f) (hp:IsUnit f.det) (hn:IsUnit n.det): m⁻¹=f*n⁻¹*fᵀ:=by
   apply inv_eq_right_inv
   have he : fᵀ*(m*f*n⁻¹*fᵀ)=fᵀ*1:=by
      rw [← Matrix.mul_assoc fᵀ,← Matrix.mul_assoc fᵀ,← Matrix.mul_assoc fᵀ, ← h,mul_nonsing_inv n hn,Matrix.one_mul,Matrix.mul_one]
   rw [← Matrix.one_mul (m*_)]
   rw [← nonsing_inv_mul fᵀ (by rwa [det_transpose]), Matrix.mul_assoc, show m*(f*n⁻¹*fᵀ)=_ from ?_, he]
   rw [← Matrix.mul_assoc,nonsing_inv_mul _ (by rwa [det_transpose]), Matrix.mul_one];
   all_goals simp only [Matrix.mul_assoc]
variable (μ : ℝ)(Q : Matrix (Key F G) (Bodies G c f) ℝ)(h0 : IsUnit (hessian F t p R 0 0).det)
 (ht:Shell S t p R (1:Config G c) (1:Joint G c f))(hu:0< μ)
 (hS:S.patch.Branches S.kernel G){σ A Λ:ℝ}(hr:R.Bounds p σ A Λ)
include ht h0 hu hS hr
lemma slab_model (hB:Q*rangers F G=1)(hC: Q*stood S (1:Joint G c f)=0):
   let A:= shear (fedora S t (G:=G)) 1; let N:= medals S t p R μ (fedora S t) 1 1; (hessian F t p R 0 0)⁻¹=Q*A*N⁻¹*(Q*A)ᵀ∧IsUnit N.det := by
   intro D N; let H:= damage (helmets G c f) (canon S t p R 1 1) 0; let L:= cannonade S t μ 1 (1:Joint G c f); let W:=(1:Joint G c f)
   let B:= medals S t p R μ 1 1 1; let T:= rangers F G
   have hx : Thaw (fun _:ℝ=> W) 0:= Thaw.fixed _ _
   have hp : Explosives S t 1 W := (explosive S t hS root_customs hx rfl).self_of_nhds
   have hA := (atire_out (fedora_style hS t) hx rfl).self_of_nhds
   have hD : D.det=1:= shear_det _ _ hA
   have hh : (M μ (fedora S t) 1 W)=Dᵀ*B*D:= by have he:dress (fedora S t) W=W:= dressed_one (fedora_style hS t); exact (by simpa only [he] using abides S t p R μ (fedora S t) 1 W hA (he.symm ▸ hp) (he.symm ▸ ht))
   have hf : N=Dᵀ*B*D:=hh
   let H':= stood S (1:Joint G c f); let Z:= hessian F t p R 0 0
   have hu' : IsUnit (grenade μ W.1).det:= fund_det (grenade_safe _ hu)
   have heB : (abode S F (1:Config G c) 0)=W:=abode_zero ..
   have he := shell_bound F t ht
   have hT := Ne.isUnit (show ((paste_sides H' T).submatrix (march F G) id).det ≠ 0 from by
      intro h; have hv: (pawns F (1:Config G c) 0).det=0:=by unfold pawns; rw [heB]; exact h
      have H:= commandment F (1:Config G c) 0; rw [hv] at H; norm_num at H)
   have hW : IsUnit B.det:= by
      have h := root_determines F (p:=p) (R:=R) (μ:=μ) 1 0 t hS hr; rw [heB] at h; specialize h ht hp; change B.det=(grenade μ W.1).det^2*(Tᵀ*H*T).det at h; change Z=Tᵀ*H*T at he; rw [h,← he]; exact (hu'.pow _).mul h0
   have hN : IsUnit N.det := by rw [hf,det_mul,det_mul,det_transpose,hD,one_mul,mul_one]; exact hW
   refine ⟨?_,hN⟩
   have hA:L*H'=grenade μ W.1:= count_ammo S t μ hS hp
   have hv:B=H+Lᵀ*L:= by unfold B medals; rw [cannon_law]; rfl
   rw [stands H L H' T (by rw [hA]; exact hu') (honors S _ hS hr t ht) (damage_symm _ ht.1) hW hv Q hB hC (march F G) hT _ he h0, sheer N B _ hf (by rw [hD]; simp) hN]; simp only [Matrix.mul_assoc,transpose_mul]
end
end YM.AllOrder.Iron
