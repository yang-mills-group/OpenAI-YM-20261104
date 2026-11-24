import YM.RG11Scheme.Stencil.Square

/-! Native transport first jet. Bridges the path-dependent *actual bare definition* `plateU`, rather than assuming a continuumized Taylor expansion on the anchors. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.RG11Scheme.Stencil.Spark
open Filter Function Lattice Set Mesh Pert Pert.First Gauge
open scoped BigOperators Classical Matrix.Norms.Frobenius Topology ContDiff
variable {G:Gauge} {X:Type} [AddCommGroup X] [One X]
local notation "Δ" => tensor X G

def went (t:Step) (x:Four X) : Δ→ₗ[ℝ] G.Color := if t.neg then - take (t.used x) else take (t.used x)
def channel (x:Four X) : Walk → (Δ→ₗ[ℝ] G.Color)
  | [] => 0
  | t::l => went t x + channel (x+t.vec) l
lemma catapult (t:Step) (x:Four X) (f:Four X→G.Color) : went t x (tremor f)= f x - f (x+t.vec) := by cases h:t.neg<;> simp [went,take,h,Lattice.Step.used,tremor, Lattice.Step.vec,sub_eq_add_neg]
lemma arrives (k:Walk) (x:Four X) (f:Four X→G.Color) : channel x k (tremor f)= f x-f (stop x k) := by induction k generalizing x with|nil=> simp [channel,stop]| cons t k ih=> simp [channel,catapult,ih, stop]

def ride (A : Δ)(l:stepL X) := G.lieExp (A l)
lemma signed_read (t:Step)(x:Four X)(A : Δ)(r:ℝ) : t.read (ride (r • A)) x=G.lieExp (r • went t x A) := by cases h:t.neg <;> simp [went,take,Step.read, h,ride,Work.F03.exp_neg_color]

lemma pulse_nil (x:Four X) : Tried (G.mat ∘ (fun (_:ℝ) => travel (ride (0:tensor X G)) x [])) 0 0 := by
    convert! glow_tried using 1; funext s; unfold comp; rw [travel]; simp [glow]
lemma transport (τ:Walk)(x:Four X) (A:Δ) : ∃ z:G.Color,Tried (G.mat ∘ (fun r:ℝ=>travel (ride (r • A)) x τ)) (channel x τ A) z := by
    induction τ generalizing x with
    | nil => exact ⟨0, pulse_nil x⟩
    | cons t τ IH =>
       obtain ⟨C,hC⟩:= IH (x+t.vec)
       refine ⟨0+C+G.ad (went t x A) (channel (x+t.vec) τ A),?_⟩; simp only [travel,signed_read t]; exact glow_tried.product hC
lemma tried_inv {p:ℝ→G.El} {u v:G.Color} (h : Tried (G.mat ∘ p) u v) : Tried (G.mat ∘ (fun r=> (p r)⁻¹)) (-u) (-v) := by
   obtain ⟨J,E,H,K⟩:=h.slope_eq
   have he : G.mat ∘ (fun r=> (p r)⁻¹) = fun r=> star ((G.mat ∘ p) r) := by funext; rw [Function.comp_apply, G.mat_inv]; exact rfl
   rw [he]; refine ⟨by rw [h.value_eq,star_one],_,?_,fun t=> (H t).star,?_⟩
   · change star (J 0)=_; rw [E,G.colorMat_skew,map_neg]
   apply K.star.congr_deriv
   simp only [defect,map_neg,star_add,star_pow,G.colorMat_skew,add_comm]

lemma same_self (v:G.Color) : G.ad v v=0 := by apply G.colorMat_injective; simp
lemma tried_adj {p q:ℝ→G.El} {u v w t:G.Color} (h:Tried (G.mat ∘ p) u v) (ht:Tried (G.mat ∘ q) w t) : Tried (G.mat ∘ (fun r=>p r * q r * (p r)⁻¹)) w (t+2 • G.ad u w) := by
   have H:= (h.product ht).product (tried_inv h)
   rw [show u+w+(-u)=w by abel, show v+t+G.ad u w+(-v)+G.ad (u+w) (-u) = t+ 2 • G.ad u w by rw [map_add,LinearMap.add_apply,map_neg,map_neg,ad_rev u w,same_self]; abel] at H
   convert! H using 1
lemma tried_square (i j : Axis)(x:Four X)(A:Δ) : Tried (G.mat ∘ (fun r:ℝ=>travel (ride (r • A)) x (square i j))) (curlAt x i j A) (bracketAt x i j A) := by
    let a := A (x,i)
    let b := A (x+step i,j)
    let c := -A (x+step j,i)
    let d := -A (x,j)
    rw [show G.mat ∘ _ = square_path a b c d from funext (fun r : ℝ=>by simp only [Function.comp_apply,Bare.square_links,G.mat_mul,ride, Pi.smul_apply,glow_inv]; exact rfl)]
    exact square_tried

def twin (k:Walk) (x:Four X) (i j : Axis) : Δ →ₗ[ℝ] Δ →ₗ[ℝ] G.Color := duo (stop x k) i j+ 2 • meld (channel x k) (vib (stop x k) i j)
lemma twin_one (τ:Walk)(x:Four X)(i j)(A B:Δ) : twin τ x i j A B = duo (stop x τ) i j A B + G.ad (channel x τ A) (curlAt (stop x τ) i j B) + G.ad (channel x τ B) (curlAt (stop x τ) i j A) := by
   rw [twin,two_smul]; simp only [LinearMap.add_apply,meld_val,vib_eq]; module
lemma twin_second (τ:Walk)(x:Four X)(i j)(A:Δ) : iteratedDeriv 2 (fun r:ℝ=>Bare.plateU (ride (r • A)) x τ i j) 0=twin τ x i j A A := by
   let v (r:ℝ) := travel (ride (r • A)) x τ
   let p (r:ℝ) := travel (ride (r • A)) (stop x τ) (square i j)
   let F (r:ℝ):= G.mat (v r*p r*(v r)⁻¹)
   obtain ⟨w,h⟩:=transport τ x A
   rw [show (fun r:ℝ=>Bare.plateU (ride (r • A)) x τ i j)=recoverL G ∘ F from funext (fun t:ℝ=> Eq.symm ((recover_group _).symm.trans ?_))] -- orientation
   · refine (Tried.decode_second (p:=F) (tried_adj h (tried_square i j (stop x τ) A))).trans ?_; rw [twin_one,dface];abel
   exact G.curvature_conjugate ..
lemma twin_first (τ:Walk)(x:Four X)(i j)(A:Δ) : deriv (fun r:ℝ=> Bare.plateU (ride (r • A)) x τ i j) 0 = curlAt (stop x τ) i j A := by
   let P r:=travel (ride ((r:ℝ) • A)) (stop x τ) (square i j)
   let V r:=travel (ride ((r:ℝ) • A)) x τ
   let Q r:= V r*P r*(V r)⁻¹
   obtain ⟨w,h⟩:=transport τ x A
   obtain ⟨f,e,he,-⟩:= Tried.slope_eq (p:=G.mat ∘ Q) (tried_adj h (tried_square i j (stop x τ) A))
   let p:=he 0
   have he' : (fun r:ℝ=>Bare.plateU (ride (r • A)) x τ i j)=recoverL G ∘ (G.mat ∘ Q) := funext fun r=> Eq.symm ((recover_group _).symm.trans (G.curvature_conjugate ..))
   rw [he', ((recoverL G).hasFDerivAt.comp_hasDerivAt _ p).deriv,e]
   change G.projectColor ((1/2:ℝ) • (G.colorMat _-star (G.colorMat _)))=_
   rw [G.colorMat_skew, sub_neg_eq_add,←two_smul ℝ,smul_smul];norm_num
lemma twin_center (τ:Walk)(x:Four X)(i j)(A:Δ)(ε:Four X→G.Color) : twin τ x i j A (tremor ε)+ curlAt (stop x τ) i j (arc ε A)= G.ad (ε x) (curlAt (stop x τ) i j A) := by
   rw [twin_one, arrives,peaks_flat,map_zero,add_zero,add_right_comm,key_ward,map_sub,LinearMap.sub_apply]; abel
end YM.RG11Scheme.Stencil.Spark
