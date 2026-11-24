import YM.Integration.WilsonOriginalStarSceneRows
import YM.RG04B.Start.Clock

/-! A single radius election for the independently addressed reporting roster.
All rents are on the true paths and original source coordinates, before tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalStarSceneRent
open Function Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Earn Sunrise
open PhysicalNext.Repeat.Legato WilsonOriginalStarSceneWords WilsonOriginalStarSceneRows
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {V T : Type} [DecidableEq V] [Fintype V]
  (d : V → ℕ) {n : Side} (o : V → Site n) (σ g τ : ℝ)
  (v : (j:V)→R.family.label (d j)) (t : V→T→ℂ)

def stencil : Entry R d → ℝ
  | .inl _ => 1
  | .inr ⟨j,s⟩ => (2:ℝ)^(WilsonOriginalStarLaurentWallet.lag R (d j) s) *
       ‖WilsonOriginalStarLaurentWallet.shape R (d j) s‖

omit [DecidableEq V] [Fintype V] in
theorem controlled {K : ℝ} (cap : ∀ j,(R.family.labels.level (d j)).coeffSize (v j) ≤ K)
    (ready : 0 ≤ g) (warm : 0<τ) (band:g ≤ 2*τ) (i : Entry R d) :
    ‖scalar R d g τ v i‖ ≤ K*stencil R d i := by
  rcases i with j|⟨j,w,s⟩
  · change ‖v j 0‖ ≤ K*1
    rw [mul_one]
    exact (single_le_sum (f:=fun i=>‖v j i‖) (fun _ _=>norm_nonneg _) (mem_univ _)).trans (cap _)
  · let F:=R.family.labels.level (d j)
    let z:=WilsonOriginalStarLaurentWallet.lag R (d j) ⟨w,s⟩
    let c:=WilsonOriginalStarLaurentWallet.shape R (d j) ⟨w,s⟩
    have key : ‖(F.core (v j)) w‖ ≤ K:=
      (single_le_sum (f:=fun i=>‖(F.core (v j)) i‖) (fun _ _=>norm_nonneg _) (mem_univ _)).trans
        ((Work.G08.size_core F (v j)).trans (cap _))
    have rate : (g/τ)^z ≤ (2:ℝ)^z := pow_le_pow_left₀ (div_nonneg ready warm.le) ((div_le_iff₀ warm).mpr band) _
    change ‖(((g/τ)^z:ℝ):ℂ)*(F.core (v j) w)*c‖ ≤ K*((2:ℝ)^z*‖c‖)
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (div_nonneg ready warm.le) _)]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul rate key (norm_nonneg _) (by positivity)) (norm_nonneg _)).trans_eq (by ring)

def wallet := ∑i:Entry R d,(1 + normalizer (raw R d i) σ * stencil R d i) *
     Real.exp (σ*(raw R d i).length)

omit [DecidableEq V] in
theorem allowance {K : ℝ} (non : 0 ≤ K) (cap : ∀ j,(R.family.labels.level (d j)).coeffSize (v j) ≤ K)
    (ready : 0 ≤ g) (warm : 0<τ) (band : g ≤ 2*τ) :
    bill R d σ g τ v (fun _=>1) ≤ (1+K)*wallet R d σ := by
  rw [bill,wallet,Finset.mul_sum]
  apply sum_le_sum
  intro i _
  have z:0 ≤ stencil R d i:=by cases i <;> simp [stencil]
  have h:=mul_le_mul_of_nonneg_left (controlled R d g τ v cap ready warm band i) (positive (raw R d i) σ).le
  unfold wage
  rw [one_mul, ←mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
  have b:=mul_nonneg (positive (raw R d i) σ).le z
  nlinarith only [h,b,non]

theorem appointed {K Ω : ℝ} (non : 0 ≤ K) (cap : ∀ j,(R.family.labels.level (d j)).coeffSize (v j) ≤ K)
    (ready : 0 ≤ g) (warm : 0<τ) (band:g ≤ 2*τ) (one:1 ≤ Ω)
    (ht : ∀i x,‖t i x‖ ≤ 1) (order count stage vac coarse : ℕ)
    (load : Fintype.card V ≤ count) (fit : maximum R d ≤ order) (room : order+1 ≤ stage)
    (future : order ≤ coarse) (stamp : tariff R d ≤ coarse)
    (cover : order+Fintype.card V*tariff R d ≤ AllOrder.Burn.horizon vac+2) :
    let E:=max 1 ((1+K)*wallet R d σ)
    let w:=fun _ : V=>(E*Ω)⁻¹
    let M:=rows R d o σ g τ v t
    Scene.Armada M w (fun _=>tariff R d) σ Ω⁻¹ order count (Fintype.card V*tariff R d) ∧
      Mentor.Cruise.Voter M σ order count stage vac coarse ∧
      ∀ j:(Stock.census V).Mode, Poly.toll w j*(E*Ω)^j.val.card=1 := by
  let E:=max 1 ((1+K)*wallet R d σ)
  have hE : 1 ≤ E:=le_max_left ..
  have hΩ:1 ≤ E*Ω:=one_le_mul_of_one_le_of_one_le hE one
  let M:=rows R d o σ g τ v t
  let X:=fleet R d o σ g τ v t (fun _=>1) (fun _=>zero_lt_one) ht order count _ fit load le_rfl
  have base: bill R d σ g τ v (fun _=>1) ≤ E:=(allowance R d σ g τ v non cap ready warm band).trans (le_max_right ..)
  have scaled := X.stored hΩ
  have fee : (E*Ω)⁻¹ * bill R d σ g τ v (fun _=>1) ≤ Ω⁻¹ := by
    calc _ ≤ (E*Ω)⁻¹*E:=mul_le_mul_of_nonneg_left base (inv_nonneg.mpr (zero_le_one.trans hΩ))
         _ = _ := by field_simp
  refine ⟨?_,⟨fun i=>?_, X.quota,room,fun C=>?_⟩,fun j=>?_⟩
  · have rad : Stoop.radius (fun _ : V=>1) (E*Ω) = fun _=>(E*Ω)⁻¹ := by
      funext i
      exact one_div _
    rw [←rad]
    exact scaled.higher fee
  · exact ⟨X.honor _,X.purchases.spend _,((X.purchases.usable i).1).trans future,stamp⟩
  · rw [Press.tall M C (fun _=>tariff R d) X.purchases.usable]
    exact (Nat.add_le_add_left (X.crew _) _).trans cover
  · change (∏ _∈j.val,(E*Ω)⁻¹)*(E*Ω)^j.val.card=1
    rw [prod_const,inv_pow,inv_mul_cancel₀ (pow_ne_zero _ (zero_lt_one.trans_le hΩ).ne')]

end YM.Integration.WilsonOriginalStarSceneRent
