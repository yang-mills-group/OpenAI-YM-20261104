import YM.RGComparison01.Post.Polar
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Marlin.Pylon
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Post.Polar
open Function Filter Set Lattice Wilson RG RG.Shoot Ovens
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup Averaging AnalyticBridge.VerifiedReset.Geo Progress.DirectedRecipe Extra.Iteration Push.BetaTransport Push.AbsoluteSums
open UVNext.CouplingReset
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Ovens.Pipes PhysicalNext PhysicalNext.Repeat Marlin
/-! Unwidened fusion. Need extra apertures only when producing NEXT
log terms. (Not claiming a retain permission through a change of basis.) -/
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ H w d ζ : ℝ} {X : Listing G n} {v : Collection.Source G n}
def merged (R : PathData G) (c : Clip) (p : BudgetPoint) (X : Pipes G n) (d : Tap G n) (β v : ℝ) : Rep G n:= ⟨R,c,fused (Marlin.hak X) p d,p,β,v⟩
variable {U:Pipes G n} {a:Tap G n}
lemma slate (h: Ingredients U a p d ζ): (fused (Marlin.hak U) p a).Valid p d ζ:= by
   obtain ⟨κ,w',u,h,hP,hZ⟩:= h.pays
   obtain ⟨ha,hb⟩:= Work.H03.answer G n U a (hak U) d u p h
   exact ⟨⟨h.stamp.regular.smooth,h.stamp.regular.at_flat,h.stamp.regular.vanish⟩,ha,hb,h.stamp.boundE,Work.H02.answer G n U a (hak U) d u κ w' ζ p hZ h hP⟩
lemma knitted (h: Ingredients U a p d ζ)(x:Config G n): (fused (Marlin.hak U) p a).gas p x=(U.pours a).gas p x * Real.exp (∑' i,a.logarithm i x):= by
   obtain ⟨κ,w',u,h,hP,hZ⟩:= h.pays; exact (Work.H01.gathered h x (F:=hak U)).tsum_eq
variable (g:G.Simple)(h:Collection.Local X p v H w)(hR:R.Bounds c σ C Λ)(hD: WilsonStartup.Decent c p)(hW:AnalyticBridge.VerifiedReset.Geo.Width p c σ)(hn:20<n.val) (α β τ :ℝ)
   (hZ:Fees G p c σ C α H w d ζ)
local notation "K"=> (shelves X R p)
local notation "u"=> branch X R c p v α
local notation "Δ"=> (Averaging.delta (X.read v))
def fusedPose (v:Collection.Source G n) (p:BudgetPoint) (X:Listing G n)(R:PathData G)(c:Clip) (α β τ:ℝ):= merged R c p (shelves X R p) (branch X R c p v α) (β+α+(Averaging.delta (X.read v))) (vac v τ)
local notation "P'"=> fusedPose v p X R c α β τ
include g h hR hD hW
lemma local_charge : ((K).pours (u)).EBound p (regularNeed G p c σ C α H):= by
   obtain ⟨k,h',ht⟩:= h.cheap
   have ht' := delta_bound g h.projects; obtain ⟨hX,hK⟩:= Collection.Local.quote_family hR hD hW α Δ h' ht ht'; exact ⟨_,fun i=> Collection.Local.quote_regular g hR hD α Δ h' h.smooth (numbering _ i),fun x=> Cost.equiv (numbering _) (hX x)⟩
include hn hZ
lemma real_charge : (P').Lawful σ C Λ d ζ:= ⟨hR,slate (h.renew g hR hD hW α hn hZ)⟩
lemma restored (x:Config G n): (P').eval x=earlyValue X R c p v β τ α x:= by
    rw [← h.raw_evaluator g hR hD hW α hn β τ]; change Real.exp _*(fused (Marlin.hak K) p (u)).gas p x=Real.exp _*((K).pours (u)).gas p x *Real.exp _; rw [knitted (a:=(u)) (h.renew g hR hD hW α hn hZ),mul_assoc]; rfl
end YM.RGComparison01.Post.Polar
