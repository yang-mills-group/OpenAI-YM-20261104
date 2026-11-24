import YM.RG06.Continuum.Glyph

/-!
# Radial-test operator quotient onto common labels
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Continuum
open Labels Analysis Maxwell Function
open scoped Matrix.Norms.Frobenius Topology ContDiff BigOperators
variable {G:Gauge}

def changeColor (A: Connection G)(u:G.El): Connection G:= fun i x=> G.adjoint u (A i x)

lemma rot_bracket (u:G.El)(x y:G.Color): G.ad (G.adjoint u x) (G.adjoint u y) = G.adjoint u (G.ad x y):=by
  apply G.colorMat_injective
  simp only [G.colorMat_ad,G.mat_adjoint, Gauge.conjugate, mul_sub, sub_mul,mul_assoc]
  -- commute brackets only
  simp only [← mul_assoc (star (G.mat u))]
  -- noncomm simplifying under nested *_
  simp

lemma ordinary_cov (g:ℝ)(A:Connection G)(h:Smooth A)(u:G.El)(a b:Axis): curvature g (changeColor A u) a b= fun x=> G.adjoint u (curvature g A a b x):=by
  funext x
  have he(a b) : par b (changeColor A u a)= fun y=> G.adjoint u (par b (A a) y):= par_linear (G.adjoint u).toContinuousLinearMap (h a) b
  unfold curvature; rw [he a,he b]
  simp [bracket, changeColor,rot_bracket,map_smul]

lemma derivative_cov (g:ℝ)(A:Connection G)(u:G.El)(i:Axis)(f:Continuum.Section G)(h:Good f) :
    covariant g (changeColor A u) i (fun x=> G.adjoint u (f x))=fun x=>G.adjoint u (covariant g A i f x):=by
  have he : par i (fun x=> G.adjoint u (f x))= fun x=>G.adjoint u (par i f x):=par_linear (G.adjoint u).toContinuousLinearMap h i
  unfold covariant; rw [he]; funext x; simp [changeColor, bracket, rot_bracket]

lemma nth_cov (g:ℝ)(A:Connection G)(h:Smooth A)(u:G.El){j:ℕ}(w:Fin j→Axis)(f:Section G)(hf:Good f):
    nablas g (changeColor A u) w (fun x=> G.adjoint u (f x))=fun x=>G.adjoint u (nablas g A w f x):=by
  induction j with
  | zero=> rfl
  | succ j H=>simp_rw [nablas,H,derivative_cov g A u _ _ (Smooth.higherCov g A h _ _ hf)]
lemma spin_curved (A:Connection G)(h:Smooth A)(g:ℝ)(u:G.El)(x:E4):
    Form.evaluate g (changeColor A u) x = Form.spin u (Form.evaluate g A x):=by
  funext j i a w
  unfold Form.evaluate Form.spin covJet; rw [ordinary_cov g A h u,nth_cov g A h u _ _ (Smooth.F g A h i a)]; exact (map_smul ..).symm

lemma radialized (d:ℕ)(J:Labels.Jet G)(u:G.El):radField d (Labels.colored u J)=changeColor (radField d J) u:=by
  unfold changeColor radField Source.potential; funext i x
  simp [Labels.colored,map_sum]

namespace Form

def bridge (g:ℝ){d:ℕ}: Field G d→ₗ[ℂ] Label G d:= ((toCommon (↑g)).comp (localSpace G d).subtype).codRestrict (Labels.localFields G d) (by
  intro p
  change toCommon _ p.val∈Labels.localFields G d
  refine ⟨scope p.property.1,?_⟩
  intro q u
  rw [radial_checks p (Labels.colored u q),radial_checks p q,radialized]
  unfold actual; rw [spin_curved _ (rad_smooth d q)]; exact p.property.2 _ _)
lemma retract {d:ℕ} (p:Label G d)(g:ℝ):bridge g (asGlyph p)=p:= Subtype.ext (rebound p g)

/-- Does not use BRST/EOM, only polynomial connections in radial gauge. Later show the kernel is
the 4D classical polynomial identity kernel, still BEFORE field-frame matching or contact terms
on separated physical limit. Keep lifts on the independent continuum side till allowed projection. -/
def radical (G:Gauge)(g:ℝ)(d:ℕ):=LinearMap.ker (bridge g (G:=G) (d:=d))
lemma radial_tests {d:ℕ}(p:Field G d)(g:ℝ):p∈radical G g d ↔ ∀ J:Labels.Jet G, actual g (radField d J) 0 p.val=0:=by
  simp_rw [← radial_checks]
  change bridge g p = 0 ↔ _
  constructor
  · intro h J; have he := congrArg (fun z:Label G d=>Labels.read J z.val) h; change _ = Labels.read J 0 at he; exact he.trans (map_zero _)
  intro h; apply Subtype.ext; exact Labels.eval_ext _ _ fun A=> (h A).trans (map_zero (Labels.read A)).symm

def QuotEquiv (G:Gauge)(d:ℕ)(g:ℝ) : (Field G d ⧸ radical G g d)≃ₗ[ℂ] Label G d:= LinearMap.quotKerEquivOfSurjective _ fun x=> ⟨_,retract x g⟩

/-- Restrict *the demand*, not the render. -/
def across (G:Gauge){d e:ℕ}(h:d ≤ e): Field G d→ₗ[ℂ] Field G e:=Submodule.inclusion (inf_le_inf_right _ <| MvPolynomial.restrictSupport_mono _ fun _ hb=> le_trans hb h)
lemma bridge_trans {d e:ℕ}(g:ℝ)(p:Field G d)(h:d≤e):bridge g (across G h p)=raiseLabel G h (bridge g p):=rfl
lemma from_trans {d e:ℕ}(p:Label G d)(h:d≤e): asGlyph (raiseLabel G h p)=across G h (asGlyph p):=rfl
end Form
end YM.RG06.Continuum
