import YM.Integration.WilsonCoherentMayerPublishedGross

/-! The filed salary itself has the original hit reserve of each genuine
marked row. This estimate precedes evaluation of its Laurent factor. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMarkedSalaryHit
open Function Filter Finset Lattice Wilson RG Marker Ac Gauge
open Push Push.AbsoluteSums Paths Animals QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise QuadraticLocal.Poetry
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V I T : Type} [DecidableEq V] {P : Passport n V} {J : Census V}

theorem original (X : I→Row P J G T) (w : V→ℝ) (t : V→ℕ) (B : BudgetPoint)
    {g U σ C a ξ : ℝ} {j k l : ℕ} (L : Scene.Armada X w t σ C j k l)
    (fund : Invoice.Supports B U a g σ ξ) :
    Hit (fun i=>(X i).ground B) B.B (fun i=>Poly.toll w (X i).mode*(X i).salary) a
      (Invoice.price B U (j+l+1) k a ξ G*C) := by
  let s:=j+l+1
  let ρ (i:I):=Poly.toll w (X i).mode*(X i).salary
  let z (i:I):=(X i).center
  let ℓ (i:I):=(X i).length
  let T₀ (i:I):=(X i).ground B
  let p:=B.power*B.order+Invoice.memories B s
  let fee:=Invoice.liberty G (B.power*B.order) s B.power B.order B.B U
  obtain ⟨_,_,hU,_,_,width⟩:=fund
  have rank i : (X i).lamp.r ≤ s := (Scene.Armada.degreeR _ L.toMinistry (X i) (L.purchases.usable i)).2.2
  have hr i : 0<ρ i:=mul_pos (Poly.worth L.positive _) (X i).sound
  have root : Footprint.Anchored z ρ ℓ σ C := by
    intro y
    convert L.suggests y using 1
    funext i
    dsimp only [ρ,z,ℓ]
    split
    next h=>unfold Row.height;ring
    next=>rfl
  have hc : 1 ≤ fee:=by
    unfold fee Invoice.liberty
    apply one_le_mul_of_one_le_of_one_le
    · exact one_le_mul_of_one_le_of_one_le (Invoice.settledP G B.power s B.order) (one_le_pow₀ hU)
    · exact one_le_pow₀ (by linarith only [Nat.cast_nonneg (α:=ℝ) B.B])
  have scale (i:I) : ρ i  ≤  fee*ρ i*(1+(ℓ i:ℝ))^p := calc
    _  ≤  fee*ρ i:=le_mul_of_one_le_left (hr i).le hc
    _  ≤  _:=le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans hc) (hr i).le)
      (one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _)))
  intro x
  have receive := Footprint.assigned_tail (id : Site n→Site n) 1 (fun _=>by simp) z ρ
    (fun i=>(hr i).le) ℓ T₀ root (B.B+2) p B.B (fun i y hy=>?_) (fun i=>?_)
    (zero_le_one.trans hc) width ρ (fun i=>(hr i).le) scale 0 x (v:=Invoice.tax s k)
  rotate_left
  · rw [id_eq,separation_comm]
    exact (Row.near (X i) _ y hy).trans (by unfold Row.radius ℓ;nlinarith)
  · let tr:=X i
    have positive : 0<(B.B:ℝ):=Nat.cast_pos.mpr B.B_pos
    have counted : B.B*coverNumber B.B (T₀ i) ≤ (1000+s+k)*B.B+ℓ i := (tr.tiles B.B B.B_pos).trans (by
      unfold tr
      gcongr <;> first | apply rank | apply L.quota)
    unfold Invoice.tax;field_simp [positive]; rw [Nat.mul_comm B.B] at counted
    exact_mod_cast counted
  have same : Footprint.payment 1 (B.B+2) p ξ fee C a (Invoice.tax s k) =
      Invoice.price B U s k a ξ G*C := by unfold Invoice.price Footprint.payment Footprint.degreeIncome;dsimp only [fee,p];ring
  simpa only [Nat.zero_le,if_true,pow_zero,mul_one,same] using receive

end YM.Integration.WilsonMarkedSalaryHit
