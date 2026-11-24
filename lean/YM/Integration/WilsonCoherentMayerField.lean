import YM.Integration.WilsonCoherentAffineIncident
import YM.RGLocalTaylor.Mayer.Moment

/-! The one-parameter physical mark in the actual Mayer orbit and Gaussian
noise sample. The saved gauge, mean shift, and exterior links are shared. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerField
open Function Lattice RG Pressure Tree Wilson Source Finset PowerSeries
open ConnectedActivityE6 RGLocalTaylor RGLocalTaylor.Insert
open PhysicalNext.Repeat.Legato Dict06.Series
open scoped BigOperators Classical ContDiff

variable {G:Gauge} {c f:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio}

def direction (X:Coat T F) (β:ℝ) (z:Coat.Air f G):Directions G f:=fun e=>
  if e∈F.trunks then 0 else if X.Hot e then (Coat.gStep β)⁻¹ • (X.liftA β z) e else 0

theorem path (X:Coat T F) (β t:ℝ) (z:Coat.Air f G) :
    X.input ((t*(Coat.gStep β)⁻¹) • X.liftA β z)=
      fun e=>G.lieExp (t • direction X β z e)*(X.input 0) e := by
  funext e
  by_cases h:e∈F.trunks
  · have tree (u:Directions G f):X.input u e=1:=F.on_tree (X.view u) ⟨e,h⟩
    simp [tree,direction,h]
  · have free (u:Directions G f):X.input u e=X.view u ⟨e,h⟩:=F.off_tree (X.view u) ⟨e,h⟩
    rw [free,free]
    by_cases hot:X.Hot e
    · simp [Coat.view,direction,h,hot,RG.increment,smul_smul]
    · simp [Coat.view,direction,h,hot]

variable (R:Run G) {I:Type} [Fintype I] (d:I→ℕ)

def written (θ:ℝ) (y:∀i,R.family.label (d i)) (o:I→Site f)
    (X:Coat T F) (β:ℝ) (z:momentSpace X) : PowerSeries ℂ:=
  let Y:=X.wrapY z.1
  ∏ i, WilsonCoherentAffineBook.book (R.family.localSection (d i))
       ((R.family.labels.level (d i)).scaled θ⁻¹ (y i))
       (expandAt (o i) (Y.input 0)) (expandAt (o i) (direction Y β z.2))

def marked (θ:ℝ) (y:∀i,R.family.label (d i)) (o:I→Site f)
    (X:Coat T F) (β:ℝ) (z:momentSpace X) (t:ℝ):ℂ:=
  let Y:=X.wrapY z.1
  ∏ i,Push.Local.presented (R.family.localSection (d i)) (o i) θ (y i)
       (Y.input ((t*(Coat.gStep β)⁻¹) • Y.liftA β z.2))

theorem received (θ:ℝ) (y:∀i,R.family.label (d i)) (o:I→Site f)
    (X:Coat T F) (β:ℝ) (z:momentSpace X) :
    ContDiffAt ℝ ∞ (marked R d θ y o X β z) 0 ∧
    ps (marked R d θ y o X β z)=written R d θ y o X β z := by
  let Y:=X.wrapY z.1
  let f' (i:I) (t:ℝ):=(R.family.localSection (d i)).evaluate
      ((R.family.labels.level (d i)).scaled θ⁻¹ (y i))
      (WilsonCoherentAffineBook.field (expandAt (o i) (Y.input 0))
        (expandAt (o i) (direction Y β z.2)) t)
  have each i:=WilsonCoherentAffineBook.source (R.family.localSection (d i))
     ((R.family.labels.level (d i)).scaled θ⁻¹ (y i)) (expandAt (o i) (Y.input 0))
       (expandAt (o i) (direction Y β z.2))
  have actual:marked R d θ y o X β z=∏ i,f' i:=by
    funext t
    simp only [marked,Finset.prod_apply]
    rw [path]
    rfl
  have all:=Dict06.Tags.ps_product f' univ (fun i _=>(each i).1)
  rw [actual]
  exact ⟨all.1,all.2.trans (prod_congr rfl fun i _=>(each i).2)⟩

theorem physical (θ:ℝ) (y:∀i,R.family.label (d i)) (o:I→Site f)
    (X:Coat T F) {β:ℝ} (hβ:0<β) (z:momentSpace X) :
    marked R d θ y o X β z (Coat.gStep β) =
      ∏ i,Push.Local.presented (R.family.localSection (d i)) (o i) θ (y i)
          ((X.wrapY z.1).input ((X.wrapY z.1).liftA β z.2)) := by
  have h:Coat.gStep β≠0:=inv_ne_zero (Real.sqrt_pos.mpr hβ).ne'
  simp [marked,mul_inv_cancel₀ h]

end YM.Integration.WilsonCoherentMayerField
