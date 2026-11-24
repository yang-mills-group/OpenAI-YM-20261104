import YM.MSbar.Duel.Pass
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Duel
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Further.GaussianScalar
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {σ ι τ:Type}[Fintype σ][Fintype τ][Fintype ι][DecidableEq ι][DecidableEq σ][DecidableEq τ]
variable {m p:ℕ}
local notation "µ"=> PowerSeries.coeff
local notation "P"=> Pot σ
local notation "Q"=> Pot ι
local notation "V"=> View σ
local notation "W"=>View ι
local notation "R"=> SpringK σ
-- concrete directional polynomial partial
local notation "H"=>SpringK σ
local notation "G"=>SpringK ι
local notation "B"=>View τ
variable (A:Matrix σ ι ℝ)(C': Matrix σ τ ℝ)(D:Matrix τ τ ℝ) (h:D.PosDef)
local notation "L"=> C'*D*C'.transpose
set_option quotPrecheck false
local notation "ν"=> PowerSeries.map (rail A).toRingHom
open MeasureTheory Set Metric
variable (F: View τ→ℝ)(T: View ι→L[ℝ] View τ)
variable (q:Pot σ)(x:View ι)(hf:Reef F 1)
local notation "ω'"=> fieldLaw D
local notation "Y"=>present A C'
local notation "j!"=> actor A C' F T
local notation "φ"=>faceA A C' F T
local notation "δ"=> fieldLaw D
include h hf
local notation "fA"=>fderiv ℝ
variable (M:ι→View τ)(b:ι→View σ)(K:Pot ι)(X₀:ι→Pot σ)(hM:Mold A C' D b M K X₀) (g:∀ i:ι,T (bolt i)=M i)(i:ι)
include hM g
-- KL variation
variable (β:SpringK σ)(hp:Kind β)
local notation "O"=> ν (confect L β)
include hp
local notation "fs"=> readScore b X₀ β
local notation "gX"=> drag A C' D F T
local notation "Q!"=> delta A C' D F T b X₀ β
-- exponential output Jets θ.W.Vector polynomial ratio vs θ.A.Payment. Variation ∆ unselected
noncomputable def mystic (K:Pot ι)(x:View ι):= Real.exp (-(eval x K))
local notation "Θ"=> mystic K
local notation "V₀"=> port K O
variable (l:List ι)
lemma swings : DifferentiableAt ℝ Θ x ∧ fA Θ x (bolt i)= -(eval x (dint (bolt i) K))*Θ x:=by
    let v(y:View ι): ℝ:= MvPolynomial.eval y K; have hv :DifferentiableAt ℝ v x:= (vent _|>.differentiable (by simp)) _; have hz : HasFDerivAt Θ (_: W→L[ℝ]ℝ) x:= hv.hasFDerivAt.neg.exp; refine ⟨hz.differentiableAt,?_⟩; rw [hz.fderiv]; change Θ x*(-(fA v x (bolt i)))= _; rw [show fA v x _= _ from dimY ..];ring -- use names
lemma bob : (Q! l x)*Θ x=buoy (Q! []* Θ) x l:=by
   induction l generalizing x with|nil=>rfl|cons i L₀ ih=>
      let A':=Q! L₀
      have he : roc (Q! []* Θ) (L₀.map Uniform.bolt)= fun x=> A' x * Θ x:=funext fun x=> (ih x).symm
      have ht:DifferentiableAt ℝ A' x:= paidRegion A C' D h F T _ x hf|>.2.differentiableAt
      unfold buoy; rw [List.map_cons,Lis.roc,he,fderiv_fun_mul ht]; rotate_left -- fill θ smooth
      · exact (swings A C' D h F T x hf M b K X₀ hM g i β hp).1
      have he := stall A C' D h F T x hf M b K X₀ hM g i β hp L₀
      obtain ⟨_,hz⟩:= swings A C' D h F T x hf M b K X₀ hM g i β hp
      change _= _ *(fA Θ x (bolt i))+ _* (fderiv ℝ A' x (bolt i)); rw [show fA A' x (bolt i)= Q! _ x + eval x (dint (bolt i) K)*A' x from he,hz];change _=_; ring
lemma mark0 : eval x (µ 0 (V₀ l))=∫ y:View τ,MvPolynomial.eval (present A C' x y) (µ 0 (fs l))∂fieldLaw D:=by
    have hx:=congr_arg (µ 0) (Duel.orbit A C' D h β b M K X₀ hM hp l)
    have hz : Kind O:=by unfold Kind; rw [PowerSeries.coeff_map,sugar L hp,_root_.map_zero]
    simp only [PowerSeries.coeff_map,elevator,Finset.sum_range_succ, Finset.sum_range_zero,zero_add,Nat.sub_zero] at hx -- covers simplify
    have hX : µ 0 (V₀ l)=rail A (bowl L (µ 0 (fs l))) := by rw [nick,elevator, sum_range_succ,sum_range_zero,zero_add,Nat.sub_zero,covers hp, covers hz,mul_one,mul_one] at hx; exact hx.symm
    rw [hX]; exact (congr_fun (clearL A x) _).trans (seen C' (A*ᵥx) h _)
-- φ/Theta trick. B^N Contdiff of convolution. solve via expression and span.T.
omit hf in
lemma lightOne : Reef (fun _ : View τ => (1:ℝ)) 1:=by
    refine ⟨contDiff_const,⟨fun l hl=> ⟨1,fun x=>?_⟩⟩⟩; cases l with|nil=> exact abs_one (α:=ℝ)|>.le|cons i l=> rw [show l=[] from List.length_eq_zero_iff.mp (show l.length=0 from (by simp only [List.length_cons] at hl; omega))]; change |fderiv ℝ (fun _ :View τ=> (1:ℝ)) x (bolt i)|≤1; simp
lemma atoms (l:List ι) : eval x (µ 0 (V₀ l))* Θ x= buoy (mystic K) x l:=by
     let F(y:B):=(1:ℝ); have hf:=lightOne A C' D h T M b K X₀ hM g β hp -- signature
     let g':= delta A C' D F T b X₀ β
     have hu(x l): g' l x=eval x (µ 0 (V₀ l)):=by have he:=mark0 A C' D h F T x hf M b K X₀ hM g β hp l; unfold g' delta drag actor; simp_rw [show ∀ i,F i=1 from fun x=>rfl,mul_one]; exact he.symm
     have hx:g' [] * Θ= Θ:= funext fun i=> by rw [Pi.mul_apply, hu,show V₀ []=1 from rfl];simp 
     have ht:=bob A C' D h F T x hf M b K X₀ hM g β hp l; change g' l x*_ =buoy (g' [] *Θ) _ _ at ht; rwa [hx,hu] at ht
end YM.MSbar.Duel
