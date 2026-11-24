import YM.Dict06.Wilson.Section

/-! The independently prescribed Wilson section polynomial in a finite
left-exponential chart around a sampled compact background. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentAffineBook
open Function Filter Finset Lattice Wilson Source Labels PowerSeries
open Dict06.Series Dict06.Wil
open scoped ContDiff Topology Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {G:Gauge} {Y:Finset Cover} {d:ℕ} {F:Frame G d}

/-- The compact pivot is on the right of each positive matrix-exponential
coefficient. The original entry flag also handles starred matrix entries. -/
def ink (b:UsedEdges Y→G.El) (A:Panel Y G) (i:Source.Index G Y):PowerSeries ℂ:=
  PowerSeries.mk fun n=>flag i.2.1 i.2.2.1 i.2.2.2
    (((n.factorial:ℝ)⁻¹ • (G.colorMat (A i.1))^n)*G.mat (b i.1))

def entry (b:UsedEdges Y→G.El) (A:Panel Y G) (i:Source.Index G Y) (t:ℝ) : ℂ:=
  flag i.2.1 i.2.2.1 i.2.2.2 (G.mat (G.lieExp (t • A i.1)*b i.1))

theorem honest (b:UsedEdges Y→G.El) (A:Panel Y G) (i:Source.Index G Y) :
    ContDiff ℝ ∞ (entry b A i) ∧ ps (entry b A i)=ink b A i := by
  let L:=flag (G:=G) i.2.1 i.2.2.1 i.2.2.2
  let X:=G.colorMat (A i.1)
  let B:=G.mat (b i.1)
  let f:=fun t:ℝ=>NormedSpace.exp (t • X)
  have hf:ContDiff ℝ ∞ f:=(G.contDiff_exp.of_le le_top).comp (contDiff_id.smul contDiff_const)
  have hg:ContDiff ℝ ∞ (fun _:ℝ=>B):=contDiff_const
  have h:entry b A i=L ∘ (f*(fun _:ℝ=>B)):=by
    funext t
    simp [entry,L,f,X,B,G.mat_mul]
  rw [h]
  refine ⟨L.contDiff.comp (hf.mul hg),?_⟩
  ext1 n
  rw [ps_at]
  erw [ordinary_map (f*(fun _:ℝ=>B)) n ((hf.mul hg).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)) L]
  have e:=congrArg (PowerSeries.coeff n) (ps_mul f (fun _:ℝ=>B) hf.contDiffAt hg.contDiffAt)
  have ef:ps f=_ :=exponential X
  rw [ps_at,ps_const,PowerSeries.coeff_mul_C,ef,PowerSeries.coeff_mk] at e
  rw [e]
  simp only [ink,PowerSeries.coeff_mk,L,B,X]
  rfl

def field (b:CoverConfig G) (A:Links ℤ G.Color) (t:ℝ):CoverConfig G:=fun e=>G.lieExp (t • A e)*b e

def book (S:SectionData F) (p:F.Coeff) (b:CoverConfig G) (A:Links ℤ G.Color) : PowerSeries ℂ:=
  poly (ink (fun e=>b e.val) (restrictLog S.stencil A)) (S.evalC p)

theorem source (S:SectionData F) (p:F.Coeff) (b:CoverConfig G) (A:Links ℤ G.Color) :
    ContDiffAt ℝ ∞ (fun t=>S.evaluate p (field b A t)) 0 ∧
    ps (fun t=>S.evaluate p (field b A t))=book S p b A := by
  let f:=entry (fun e:UsedEdges S.stencil=>b e.val) (restrictLog S.stencil A)
  have obs: (fun t=>S.evaluate p (field b A t))=readPoly f (S.evalC p):=by
    funext t
    have cells:Source.entry (S:=S.stencil) (field b A t)=fun i=>f i t:=by
      funext i
      unfold f entry
      rw [flag_eval]
      rfl
    change MvPolynomial.eval (Source.entry (field b A t)) (S.evalC p)=_
    rw [cells]
    rfl
  rw [obs]
  have evaluation:=readPoly_ps f (S.evalC p) (fun i=>(honest _ _ i).1.contDiffAt)
  refine ⟨evaluation.1,evaluation.2.trans ?_⟩
  exact congrArg (fun a=>poly a (S.evalC p)) (funext fun i=>(honest _ _ i).2)

theorem flat (S:SectionData F) (p:F.Coeff) (A:Links ℤ G.Color) :
    book S p 1 A=Dict06.Wil.book S p A := by
  unfold book Dict06.Wil.book
  apply congrArg (fun f=>poly f (S.evalC p))
  funext i
  ext1 n
  simp [ink,Dict06.Wil.ink,G.mat_one]

end YM.Integration.WilsonCoherentAffineBook
