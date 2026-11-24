import YM.Integration.WilsonReportCashierPrice
import YM.Extraction.Integrate

/-! Absolute mass of the actual finite torus test.  Mesh convergence at
fixed period takes place in the original fundamental domain; restricting
that domain only decreases the limiting positive mass. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonExternalMeshMass
open Function Filter Finset Set MeasureTheory Metric Lattice Wilson Extraction RG17
open WilsonReportFineSmear
open scoped Topology Classical BigOperators
variable {G:Gauge} (C:Family G) {n:ℕ}

def charge (T:Points n→ℂ) {N p:ℕ} (y:Var C.S n N p) : ℂ :=
  (C.S.a N:ℂ)^(4*n)*T (Order.cells C N p y)

def basis (T:Points n→ℂ) (N p:ℕ) (x:Points n) : ℂ :=
  stair C.S (fun y:Var C.S n N p=>T (Order.cells C N p y)) x

theorem bill (T:Points n→ℂ) (N p:ℕ) :
    (∫ x:Points n,‖basis C T N p x‖)= ∑y:Var C.S n N p,‖charge C T y‖ := by
  let c (y:Var C.S n N p):ℂ:=↑‖T (Order.cells C N p y)‖
  have same : (fun x:Points n=>(↑‖basis C T N p x‖:ℂ))=stair C.S c := by
    funext x;by_cases hx:x∈Fund C.S p n
    · simp only [basis,stair,hx,indicator_of_mem,c]
    · simp only [basis,stair,indicator_of_notMem hx,norm_zero,Complex.ofReal_zero]
  have equal := stair_integral (S:=C.S) c
  rw [←same] at equal
  change (∫x:Points n,(↑‖basis C T N p x‖:ℂ))=(C.S.a N:ℂ)^(4*n)*∑y:Var C.S n N p,(↑‖T (Order.cells C N p y)‖:ℂ) at equal
  have casted:(∫x:Points n,(↑‖basis C T N p x‖:ℂ))=(↑(∫x:Points n,‖basis C T N p x‖):ℂ):=
    integral_ofReal (μ:=volume) (𝕜:=ℂ)
  rw [casted] at equal
  norm_cast at equal
  simp only [charge,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos N).le]
  rw [←mul_sum]
  exact_mod_cast equal

theorem cell {N p:ℕ} (T:Points n→ℂ) {x:Points n} (hx:x∈Fund C.S p n) :
    basis C T N p x=T (tag (C.S.a N) (address (C.S.a N) x)) := by
  unfold basis stair;rw [indicator_of_mem hx];apply congrArg T
  apply PiLp.ext;intro j
  have ok:=congr_fun (show address (C.S.a N) x=_ from found (N:=N) hx) j
  simp only [Order.cells,points_apply,tag,Schedule.place]
  exact congrArg (C.S.gridPoint N) ok.symm

theorem period (T:Points n→ℂ) (cts:Continuous T) (support:HasCompactSupport T) (p:ℕ) : Tendsto
    (fun N=>∑y:Var C.S n N p,‖charge C T y‖) atTop
    (𝓝 (∫ x:Points n,(Fund C.S p n).indicator (fun t=>‖T t‖) x)) := by
  obtain ⟨c,hT⟩:=cts.bounded_above_of_compact_support support
  let M:Points n→ℝ:=(Fund C.S p n).indicator (fun _=>c)
  have bnd:Integrable M:=(integrable_indicator_iff (full_box _ _ _).1).mpr
    (integrableOn_const (full_box _ _ _).2.ne)
  have live (N:ℕ) : AEStronglyMeasurable (fun x=>‖basis C T N p x‖) volume :=
    (stair_int (fun y:Var C.S n N p=>T (Order.cells C N p y))).aestronglyMeasurable.norm
  have dom (N:ℕ) (x:Points n) : ‖‖basis C T N p x‖‖≤M x := by
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    by_cases hx:x∈Fund C.S p n
    · rw [cell C T hx];change _≤(Fund C.S p n).indicator _ x;rw [indicator_of_mem hx];apply hT
    simp [basis,stair,M,hx]
  have point (x:Points n) : Tendsto (fun N=>‖basis C T N p x‖) atTop
      (𝓝 ((Fund C.S p n).indicator (fun t=>‖T t‖) x)) := by
    by_cases hx:x∈Fund C.S p n
    · simp_rw [cell C T hx,indicator_of_mem hx]
      exact (cts.continuousAt.tendsto.comp (chosen (S:=C.S) x)).norm
    simp [basis,stair,hx]
  simp_rw [←bill]
  exact tendsto_integral_filter_of_dominated_convergence M (Eventually.of_forall live)
    (Eventually.of_forall fun N=>ae_of_all _ (dom N)) bnd (ae_of_all _ point)

theorem funded (f:Extraction.Order) (T:Points n→ℂ) (cts:Continuous T) (support:HasCompactSupport T) {η:ℝ} (he:0<η) :
    ∀ᶠi:ℕ×ℕ in f.fuse, (∑y:Var C.S n i.1 i.2,‖charge C T y‖)≤(∫x,‖T x‖)+η := by
  change ∀ᶠ b:ℕ in atTop,∀ᶠ a:ℕ in atTop,_
  filter_upwards with b
  let p:=f.per b
  have hI:Integrable (fun x=>‖T x‖):=cts.norm.integrable_of_hasCompactSupport support.norm
  have full:(∫x,(Fund C.S p n).indicator (fun t=>‖T t‖) x)≤∫x,‖T x‖ := by
    apply integral_mono (hI.indicator (full_box _ _ _).1) hI
    intro x;by_cases hx:x∈Fund C.S p n
    · simp only [indicator_of_mem hx,le_refl]
    simp only [indicator_of_notMem hx,norm_nonneg]
  have price:=(period C T cts support p).comp f.mesh.cofinal
  have bound:=price.eventually (eventually_lt_nhds (show _<(∫x,‖T x‖)+η from full.trans_lt (lt_add_of_pos_right _ he)))
  exact bound.mono fun a ha=>ha.le

theorem regulated (f:Extraction.Order) (T:Test n) {η:ℝ} (he:0<η) :
    ∀ᶠ i:ℕ×ℕ in f.fuse,(∑y:Var C.S n i.1 i.2,‖weight C T y‖) ≤ (∫x,‖T x‖)+η :=
  funded C f T T.continuous T.hasCompactSupport he

end YM.Integration.WilsonExternalMeshMass
