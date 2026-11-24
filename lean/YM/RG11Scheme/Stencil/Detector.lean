import YM.RG11Scheme.Stencil.Trail
import YM.Pert.First.Completion

/-! On every raw lattice curvature letter, with derivatives; exact first two link expansion coefficients and their local gauge identity. -/
set_option autoImplicit false
set_option maxHeartbeats 160000
set_option maxRecDepth 8000
noncomputable section
namespace YM.RG11Scheme.Stencil.Cell
open Function Set Filter Lattice Mesh Pert Pert.First Labels Spark Bare
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {X : Type} [AddCommGroup X] [One X] {G:Gauge} {j k d:ℕ}
local notation "Δ" => Spark.tensor X G
local notation "Σ!" => (Fintype.card Signed)

def clasp (x:Four X) (i k:Axis)(γ:Fin j→Axis) : Δ →ₗ[ℝ] Δ →ₗ[ℝ] G.Color := (j.factorial:ℝ)⁻¹ • ∑ s:Finset (Fin j), Bare.sign s • twin (Bare.walk γ s) x i k

def expander (j:ℕ)(x:Four X) : Δ →ₗ[ℝ] Δ →ₗ[ℝ] Response G j where
   toFun A := LinearMap.pi (fun i=>LinearMap.pi fun k=>LinearMap.pi fun γ=> clasp x i k γ A)
   map_add' A B := by apply LinearMap.ext; intro w; funext i k γ; change (clasp x i k γ) (A+B) w=_; rw [map_add]; exact rfl
   map_smul' r A := by apply LinearMap.ext;intro w;funext i k γ; change (clasp x i k γ) (r • A) w=_; rw [map_smul]; exact rfl

lemma active (A B:Δ)(x:Four X)(i k:Axis)(γ:Fin j→Axis) : expander j x A B i k γ=(j.factorial:ℝ)⁻¹ • ∑ s:Finset (Fin j),Bare.sign s • twin (Bare.walk γ s) x i k A B := by
   change clasp x _ _ _ _ _=_; simp [clasp,LinearMap.sum_apply]
lemma shear (A:Δ)(x:Four X)(i k:Axis)(γ:Fin j→Axis) : wideCore G j x A i k γ=(j.factorial:ℝ)⁻¹ • ∑ s:Finset (Fin j),Bare.sign s • curlAt (stop x (Bare.walk γ s)) i k A := by simp_rw [curl_line]; rw [wideCore_apply]; simp_rw [Bare.displaced]

def indye (u:G.Color)(A:Δ):Δ := fun l=> G.ad u (A l)
lemma curl_indye (v:G.Color)(A:Δ)(x:Four X)(i k:Axis): curlAt x i k (indye v A) = G.ad v (curlAt x i k A) := by rw [curl_line,curl_line]; simp only [indye,Bare.wideCurl,map_sub,map_add]
lemma vivid (ε:Four X→G.Color)(A:Δ)(x:Four X) : expander j x A (tremor ε)+wideCore G j x (arc ε A)=wideCore G j x (indye (ε x) A) := by
   funext i k γ; simp only [Pi.add_apply]; simp_rw [active, shear]; rw [← smul_add,← Finset.sum_add_distrib]; refine congrArg (fun v:G.Color=> (j.factorial:ℝ)⁻¹ • v) (Finset.sum_congr rfl ?_); intro s _; rw [←smul_add,twin_center,curl_indye]
lemma scrubbed (ε:Four X→G.Color)(x:Four X): wideCore G j x (tremor ε)=0 := by
   funext i k γ; simp_rw [shear,peaks_flat]; simp
lemma resin (s:Signed)(l:stepL X) (ε:Four X→G.Color) : wideLink G s (tremor ε) l = tremor (ε ∘ affine s 0) l := by
    let p:= (posDir l.2).rotate s
    have ht : affine s 0 (l.1+step l.2) = affine s 0 l.1 + p.vec := by rw [show p.vec=s.act (step l.2 : Four X) from (Step.vec_rotate ..), affine, s.act_add]; simp [affine]
    change _= ε (affine s 0 l.1) - ε (affine s 0 (l.1+step l.2)); rw [ht,←catapult p (affine s 0 l.1) ε]
    cases e:p.neg <;> simp [wideLink, went, Spark.take,←show p=(posDir l.2).rotate s from rfl,e]
lemma ember (s:Signed)(l:stepL X)(ε:Four X→G.Color)(A:Δ) : wideLink G s (arc ε A) l=arc (ε ∘ affine s 0) (wideLink G s A) l := by
    let p:= (posDir l.2).rotate s
    have ht : affine s 0 (l.1+step l.2) = affine s 0 l.1 + p.vec := by rw [show p.vec=s.act (step l.2 : Four X) from (Step.vec_rotate ..), affine,s.act_add]; simp [affine]
    rw [wideLink_apply,show (posDir l.2).rotate s=p from rfl]; unfold arc; rw [comp_apply,comp_apply,ht];cases e:p.neg <;> simp [wideLink,←show p=(posDir l.2).rotate s from rfl,Lattice.Step.used,Lattice.Step.vec,e,affine,sub_eq_add_neg]
    abel
lemma dye_wide (s:Signed)(u:G.Color)(A:Δ): wideLink G s (indye u A)=indye u (wideLink G s A) := by funext l; change _=G.ad u (wideLink G s A l); rw [wideLink_apply,wideLink_apply,map_smul]; rfl

def outside (h:ℝ)(s:Signed)(j:ℕ) : Response G j →ₗ[ℝ] Taylor G j := (Labels.Taylor.turn s.ortho) ∘ₗ (h^(-(j+2:ℤ)) • radialMap (G:=G) (j:=j))
def partial2 (h:ℝ)(s:Signed)(x:Four X)(j:ℕ) := let B:=wideLink (R:=X) G s; ((expander j (affine s⁻¹ 0 x)).compl₁₂ B B).compr₂ (outside h s j)
def full2 (h:ℝ)(x:Four X)(j:ℕ) : Δ →ₗ[ℝ] Δ →ₗ[ℝ] Taylor G j := (Σ!:ℝ)⁻¹ • ∑ s : Signed, partial2 (G:=G) h s x j

lemma sided (A:Δ)(h:ℝ)(x:Four X) : wideLinear G j h x A=(Σ!:ℝ)⁻¹ • ∑ s:Signed, outside h s j (wideCore G j (affine s⁻¹ 0 x) (wideLink G s A)) := by unfold wideLinear; rw [LinearMap.smul_apply,LinearMap.sum_apply]; simp only [outside, LinearMap.comp_apply]
lemma rung (A B:Δ)(h:ℝ)(x:Four X) : full2 h x j A B=(Σ!:ℝ)⁻¹ • ∑ s:Signed, outside h s j (expander j (affine s⁻¹ 0 x) (wideLink G s A) (wideLink G s B)) := by unfold full2; simp_rw [LinearMap.smul_apply, LinearMap.sum_apply]; simp only [partial2, LinearMap.compl₁₂_apply,LinearMap.compr₂_apply]
lemma sunlight (ε:Four X→G.Color)(A:Δ)(h:ℝ)(x:Four X): full2 h x j A (tremor ε) + wideLinear G j h x (arc ε A) = wideLinear G j h x (indye (ε x) A) := by
    simp_rw [sided,rung,dye_wide]; rw [← smul_add,← Finset.sum_add_distrib]; congr 1
    apply Finset.sum_congr rfl; intro s _; rw [←LinearMap.map_add, funext (fun l=>ember s l ε A), funext (fun l=>resin s l ε),vivid]; simp [affine]
lemma shadow (ε:Four X→G.Color)(x:Four X) (h:ℝ) : wideLinear G j h x (tremor ε)=0 := by
   rw [sided]; simp_rw [show ∀ s, wideLink G s (tremor ε)=_ from fun s=>funext (fun l=>resin s l ε),scrubbed,map_zero,Finset.sum_const_zero,smul_zero]
end YM.RG11Scheme.Stencil.Cell
