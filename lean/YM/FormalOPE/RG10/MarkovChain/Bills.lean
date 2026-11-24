import YM.FormalOPE.RG10.MarkovChain.Costs
/-!
 # real jet transport of Roof property (not support localization in space)
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.MarkovChain
open Function Filter Topology Set MeasureTheory PertExtension Precision
open BlockGauge Inherit Push.Loops Chart Lattice RG GaussianScore
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
open Line
variable {G:Gauge}{c f n:Side}
namespace Roof
variable {S:StepData c f} {H:S.patch.Branches S.kernel G}{t:S.Choices}{hf:_root_.Even f.val}{L:Fabric G c} {C:Cloth L}{P:Inside S.ratio}
local notation "M" => P.join C.choose H t hf
local notation "d" => sector S H t hf L P C.choose
local notation "Ω" => Field M
private lemma singleTransfer (a : Ω→ℝ) (ha:ContDiffAt ℝ ∞ a 0) (x x' x'' x''' : Ω)(h: (fun s:ℝ=> a (s • x) + a (s • x'))=fun s:ℝ=> a (s • x'')+a (s • x''')) (i:ℕ) : jet a i x + jet a i x'=jet a i x''+jet a i x''' := by
 have he:= Aspiration.unique ( (directions ha x).add (directions ha x')) ((show Aspiration _ _ from ?_) : Aspiration ((fun r:ℝ=> a (r•x)) + (fun r:ℝ=> a (r•x'))) ((fun i=>jet a i x'')+(fun i=> jet a i x''')))
 · exact congr_fun he i
 rw [show (fun r:ℝ=> a (r•x))+(fun r:ℝ=> a (r•x'))= _ from h]; exact (directions ha x'').add (directions ha x''')
private lemma near_law {a : Ω→ℝ}(ha:ContDiffAt ℝ ∞ a 0) (h:∀ (x:Cross (G:=G) S P),Near S H t hf P a x) (i:ℕ)(x:Cross (G:=G) S P) : Near S H t hf (T:=C.choose) P (jet a i) x:= by
 intro y z hq
 have hi:= singleTransfer (H:=H) (t:=t) (hf:=hf) a ha (d (x,y)) (d (0,z)) (d (x,z)) (d (0,y)) ?_ i
 · unfold enduring at *; change _-_=_-_; linarith [hi]
 ext1 s
 have ht:= h (s•x) (s•y) (s•z) (by rw [map_smul,map_smul,hq])
 unfold enduring at ht; change a (s • _) + a (s • _) = a (s • _) + a (s • _)
 simp_rw [←map_smul, Prod.smul_mk,smul_zero]; dsimp only at ht; linarith [ht]
-- issue argument C etc in H type.Y.St. ensure explicit.
lemma differentiated {n: Side}{L: Fabric G n} {T:Cloth L} {a:Field T.choose→ℝ}(ha:ContDiffAt ℝ ∞ a 0)(h:Roof T a) (i:ℕ):Roof T (jet a i):= by
 cases T with
 | floor=> trivial
 | @inLayer c f S H t hf L P C=>
    rw [Roof] at h ⊢
    refine ⟨near_law (C:=C) ha h.1 i,?_⟩
    let D : Field C.choose →L[ℝ] Field (P.join C.choose H t hf):= LinearMap.toContinuousLinearMap ((sector S H t hf L P C.choose).toLinearMap ∘ₗ LinearMap.inr _ _ _)
    have hh: ContDiffAt ℝ ∞ (a ∘ D) 0:= (show ContDiffAt ℝ ∞ a (D 0) from by rw [map_zero]; exact ha).comp _ D.contDiff.contDiffAt
    suffices all_eq : enduring S H t hf P (T:=C.choose) (jet a i)=jet (a∘D) i from (congr_arg (Roof C) all_eq).mpr (differentiated (L:=L) (a:= a ∘ D) hh h.2 _)
    funext x
    have he:= Aspiration.unique (directions hh x) ( (show Aspiration (fun s:ℝ=> (a ∘ D) (s • x)) (fun i=> jet a i (D x)) from by
       rw [show (fun s:ℝ=>(a∘D) (s•x))=fun s:ℝ=>a (s • D x) from funext (fun i=> congr_arg a (D.map_smul i x))]; exact directions ha _))
    exact (congr_fun he i).symm
termination_by structural T
end Roof
end YM.FormalOPE.RG10.MarkovChain
