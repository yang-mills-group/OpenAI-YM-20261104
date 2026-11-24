import YM.Integration.SignedWeightedMoment
import YM.OPE.Therm.Bath
import YM.OPE.Therm.Rite

/-! A fixed quadratic price for an original signed observable that forces
a physical plaquette at one of finitely many prescribed root sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ThermalRootedMoment
open Function Set Filter MeasureTheory Lattice Wilson RG Cells OPE.Therm OPE.Therm.House SignedWeightedMoment
open scoped Classical BigOperators Topology

theorem supported {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {E : Set X} {f : X → ℂ} (hf : Envelope f) (support : ∀ x, f x ≠ 0 → x ∈ E) :
    ‖∫ x, f x ∂μ‖^2 ≤ μ.real E * ∫ x, ‖f x‖^2 ∂μ := by
  have off (x : X) (hx : x ∉ E) : f x = 0 := by by_contra hn; exact hx (support x hn)
  have eqn : (∫ x in E, f x ∂μ) = ∫ x, f x ∂μ := setIntegral_eq_integral_of_forall_compl_eq_zero off
  have sqn : (∫ x in E, ‖f x‖^2 ∂μ) = ∫ x, ‖f x‖^2 ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp only [off x hx,norm_zero,zero_pow (by decide : 2≠0)])
  by_cases hz : μ E = 0
  · have ez := Measure.restrict_eq_zero.mpr hz
    rw [← eqn,ez,integral_zero_measure,norm_zero,zero_pow (by decide : 2≠0),
      ((measureReal_eq_zero_iff (μ:=μ) (s:=E)).mpr hz),zero_mul]
  have hm : 0<μ.real E := lt_of_le_of_ne measureReal_nonneg (fun h => hz ((measureReal_eq_zero_iff (μ:=μ) (s:=E)).mp h.symm))
  have one : (∫ _x in E, (1:ℝ) ∂μ) = μ.real E := by simp
  have j := jensen (μ.restrict E) (Envelope.const 1) (fun _ => zero_le_one)
    (show 0<(∫ _x in E, (1:ℝ) ∂μ) by rw [one]; exact hm) hf 2
  simp only [one,one_smul,one_mul,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hm.le),eqn,sqn] at j
  calc _ = μ.real E * (μ.real E * ((μ.real E)⁻¹ * ‖∫ x, f x ∂μ‖)^2) := by field_simp
       _ ≤ _ := mul_le_mul_of_nonneg_left j hm.le

variable {G : Gauge} {n : Side}

private def offset (a : PlaqAxes) (r : Fin 4) : Site n :=
  ![0,step a.val.1,step a.val.1+step a.val.2,step a.val.2] r

def incident (x : Site n) : Finset (Face (Per n)) :=
  Finset.univ.image fun r : PlaqAxes × Fin 4 => (x-offset r.1 r.2,r.1)

private theorem catches (p : Face (Per n)) {x : Site n} (h : x ∈ touched p) : p ∈ incident x := by
  rcases p with ⟨b,a⟩
  rw [touched,square_corners] at h
  simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl
  · exact Finset.mem_image.mpr ⟨(a,0),Finset.mem_univ _,congrArg (fun z : Site n => (z,a)) (sub_zero _)⟩
  · exact Finset.mem_image.mpr ⟨(a,1),Finset.mem_univ _,congrArg (fun z : Site n => (z,a)) (add_sub_cancel_right b (step a.val.1))⟩
  · refine Finset.mem_image.mpr ⟨(a,2),Finset.mem_univ _,congrArg (fun z : Site n => (z,a)) ?_⟩
    change b+step a.val.1+step a.val.2-(step a.val.1+step a.val.2)=b
    abel
  · exact Finset.mem_image.mpr ⟨(a,3),Finset.mem_univ _,congrArg (fun z : Site n => (z,a)) (add_sub_cancel_right b (step a.val.2))⟩
  · exact Finset.mem_image.mpr ⟨(a,0),Finset.mem_univ _,congrArg (fun z : Site n => (z,a)) (sub_zero _)⟩

private theorem incident_count (X : Finset (Site n)) :
    (X.biUnion incident).card ≤ X.card*(Fintype.card PlaqAxes*4) := by
  have bound (x : Site n) : (incident x).card ≤ Fintype.card PlaqAxes*4 := by
    calc _ ≤ (Finset.univ : Finset (PlaqAxes × Fin 4)).card := Finset.card_image_le
         _ = _ := by simp
  exact Finset.card_biUnion_le.trans ((Finset.sum_le_sum (fun i _ => bound i)).trans_eq (by simp))

theorem charged (μ : Measure (Config G n)) [IsFiniteMeasure μ] (X : Finset (Site n))
    {t δ : ℝ} (hδ : 0≤δ) (hits : ∀ p, μ.real (trigger p t) ≤ δ)
    {f : Config G n → ℂ} (hf : Envelope f) (fire : ∀ U, f U ≠ 0 → ∃ x ∈ X, x ∈ flags t U) :
    ‖∫ U, f U ∂μ‖^2 ≤ ((X.card*(Fintype.card PlaqAxes*4):ℕ):ℝ)*δ*(∫ U, ‖f U‖^2 ∂μ) := by
  let J := X.biUnion incident
  have forced (U : Config G n) (hU : f U ≠ 0) : U ∈ (chilly J t)ᶜ := by
    obtain ⟨x,hx,hflag⟩ := fire U hU
    obtain ⟨p,hp,hot⟩ := (flags_spec _ _ _).mp hflag
    exact fun cold => hot.not_ge (cold p (Finset.mem_biUnion.mpr ⟨x,hx,catches p hp⟩))
  have occ := (cool_miss δ hits J).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (incident_count X)) hδ)
  exact (supported μ hf forced).trans (mul_le_mul_of_nonneg_right occ (integral_nonneg (fun _ => sq_nonneg _)))

/-- The finite normalized physical coarse scene pays a true super-polynomial
hot-plaquette probability per prescribed site. The quadratic moment order
and multiplicity are independent of the lattice period and chamber count. -/
theorem rare_scene {H : History G} (Y : H.Selected) (P : Poetry H.levels) (hG : G.Simple) :
    ∀ᶠ k : ℕ in atTop, ∀ N, k≤N → ∀ (p : ℕ) (X : Finset (Site (H.S.side k p)))
      (f : Config G (H.S.side k p) → ℂ), Envelope f →
        (∀ U, f U ≠ 0 → ∃ z ∈ X, z ∈ flags (cool H.levels k) U) →
      ‖∫ U, f U ∂scene H N p k‖^2 ≤
        ((X.card*(Fintype.card PlaqAxes*4):ℕ):ℝ)*vanishP H.levels k *
          (∫ U, ‖f U‖^2 ∂scene H N p k) := by
  filter_upwards [rare (H:=H) P hG Y] with k price
  intro N hk p X f hf fire
  haveI := probability (H:=H) (p:=p) Y hk
  exact charged _ X (Real.exp_pos _).le (price N hk p) hf fire

end YM.Integration.ThermalRootedMoment
