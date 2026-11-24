import YM.Comparison.RG02.Symmetry.Pins
import YM.Comparison.RG02.Thermal.Kept
/-!
# Id of (total) cubic at first interacting grade.

Refines Layers etc.: after taking out all Haar, thermal log & constants a projected one color
vanishes. Hence in our joint-parts bookkeeping, with groups Simple, no additional terms even
on torus, not just an asympt Formula. Does NOT assert remaining cubic tensor nonzero. Installed
kinetic comparison through order two unchanged.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Symmetry.Orbit.Linked
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested
open Moving Moving.Path Moving.Shift Marker Multi Order YM.Next.SectorChange Integral Actual Laplace Valence Ribbon Thermal
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
  (K : Bulk.Kernel S p P O) (D : BudgetPoint) (F : Forest S.ratio) (w : S.Choices)
variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
  (W : Bulk.Colors R G f) (r : ℕ) (s : R.Mode)
local notation "Ω" x => Bulk.Fk K F w W x r
local notation "L"=> ground K F w W r
local notation "Z"=> Layers.base K F w
local notation "K0"=> Layers.forecast K F w
local notation "X"=> fieldDir G c 1
local notation "A"=> fderiv ℝ (Precision.thermal F w p P (K.b F) O) 0

-- choose any rank≥1 moment book, even if hW includes nontrivial insertion powers.
include D in
lemma horizontal (hW : W.Standard) (hG:G.Simple) (hr : 1≤r) : A = 0:= by
    let f := L 1; have ht(x:X): f x= -(K0 x 1:ℂ):= by unfold f ground; rw [if_neg (by decide),add_zero]; exact Wick.pays_first_log K F w W hW x hr
    let h(x:X):= Assembly.jet Z 3 x + A x
    have hs(x:X): K0 x 1=h x:= by unfold Layers.forecast h; simp [Assembly.jet]
    have h0: ContDiffAt ℝ ω Z 0:= by
        let X₀(t:X):= (t,K.b F t); have hx:X₀ 0=0:= Prod.ext rfl (K.critical F).1; exact (show ContDiffAt ℝ ω (Bulk.Surface S p P F w) (X₀ 0) from hx.symm ▸ ((K.critical F).2.2 w).1).comp (f:=X₀) (0:X) (contDiffAt_id.prodMk ((K.critical F).2.1))
    have he:= (bed K D F w W r hW.1).color_grad hr hG
    have hi(x:X): fderiv ℝ (Assembly.jet Z 3) 0 x=0:= by
       have h := Thermal.re_jet h0 1 3; rw [if_neg (by decide)] at h
       exact (iteratedFDeriv_one_apply ..).symm.trans (DFunLike.congr_fun h ![x])
    have hf: f=( -Complex.ofRealCLM) ∘ h := funext fun x=> by rw [ht,hs]; rfl
    apply ContinuousLinearMap.ext; intro x'; have he : fderiv ℝ f 0 x'=0:= DFunLike.congr_fun he x'
    let q:=Assembly.jet Z 3; let P:= A; let T := -Complex.ofRealCLM
    have hu: Differentiable ℝ q:= Tensor.diag_smooth (Tensor.coeff Z 3 0) (m:=ω) |>.differentiable (by simp)
    rw [hf,fderiv_comp _ _ _] at he
    · rw [T.fderiv,ContinuousLinearMap.comp_apply, show h=q+P from rfl,fderiv_add (hu 0) P.differentiableAt,P.fderiv] at he
      simpa [P,T,q,_root_.add_apply,hi] using he
    · exact T.differentiableAt
    exact (hu _).add P.differentiableAt

include D in
lemma fixed (hW : W.Standard) (hG:G.Simple) (hr : 1≤r) (x:X): ground K F w W r 1 x= -Complex.ofReal (Assembly.jet Z 3 x) := by
   unfold ground; rw [if_neg (by decide),add_zero]; rw [show detail _ _ 1= -(K0 x 1:ℂ) from Wick.pays_first_log K F w W hW x hr]
   unfold Layers.forecast; simp_rw [Assembly.jet,iteratedFDeriv_one_apply,horizontal K D F w W r hW hG hr]; simp
section link
variable {H:RG.History G} (Λ : Bulk.Chain H) (N m v:ℕ) (h:m<N)
    (F : Forest (H.levels.clock.op m v).ratio) (t:(H.levels.clock.op m v).Choices)
    (B : Bulk.Colors R G (H.S.side (m+1) v))
local notation "Q"=> H.rep N v m
local notation "p0"=> (fun y: fieldDir G (H.S.side m v) 1=> mainTerm (Rep.clip Q) (Rep.path Q) (represent y))
include D in
theorem id_cubic (hG:G.Simple)(hr : 1≤r)(hw:B.Standard) (x:fieldDir G (H.S.side m v) 1) : ground (Λ.step N m v h) F t B r 1 x= -Complex.ofReal (Assembly.jet p0 3 x) := by rw [fixed _ D F t B _ hw hG hr, keeps_class Λ N m v h F t 3 (by omega)]
end link
end YM.Comparison.RG02.Symmetry.Orbit.Linked
