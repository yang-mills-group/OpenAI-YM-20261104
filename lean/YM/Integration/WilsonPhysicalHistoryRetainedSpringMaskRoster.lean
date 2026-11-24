import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskPlaced

/-! Restore the filed finite upper roster, with its original powers of the
running coupling, at a fixed genuine old lattice site. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Finset Lattice RG Wilson MeasureTheory OPE.Therm
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic IterationFour IterationFour.Vacuum
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G : Gauge} {n : Side} {Ω α : Type*} [MeasurableSpace Ω]

private theorem list_mask (μ : Measure Ω) [IsFiniteMeasure μ] (f : α→Ω→ℝ) (Z : List α) {A B : ℝ}
    (paid : ∀a∈Z,Measurable (f a) ∧ (∀U,‖f a U‖≤A) ∧ (∫U,‖f a U‖ ∂μ)≤B) :
    Measurable (fun U=>(Z.map fun a=>f a U).sum) ∧
      (∀U,‖(Z.map fun a=>f a U).sum‖≤Z.length*A) ∧
      (∫U,‖(Z.map fun a=>f a U).sum‖ ∂μ)≤Z.length*B := by
  induction Z with
  | nil=>simp
  | cons a Z ih=>
    obtain ⟨ma,ca,ha⟩:=paid a List.mem_cons_self
    obtain ⟨mz,cz,hz⟩:=ih (fun k hk=>paid k (List.mem_cons_of_mem _ hk))
    let tail:=fun U=>(Z.map fun k=>f k U).sum
    have ai : Integrable (f a) μ:=Integrable.of_bound ma.aestronglyMeasurable A (Eventually.of_forall ca)
    have zi : Integrable tail μ:=Integrable.of_bound mz.aestronglyMeasurable (Z.length*A) (Eventually.of_forall cz)
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    refine ⟨ma.add mz,?_,?_⟩
    · intro U
      simpa only [add_mul,one_mul,add_comm] using (norm_add_le ..).trans (add_le_add (ca U) (cz U))
    apply (integral_mono (ai.add zi).norm (ai.norm.add zi.norm) (fun U=>norm_add_le (f a U) (tail U))).trans
    change (∫x,‖f a x‖+‖tail x‖ ∂μ)≤_
    rw [integral_add ai.norm zi.norm]
    simpa only [add_mul,one_mul,add_comm] using add_le_add ha hz

private theorem map_sub (Z : List α) (f g : α→ℝ) : (Z.map fun a=>f a-g a).sum=(Z.map f).sum-(Z.map g).sum := by
  induction Z with
  | nil=>simp
  | cons a Z ih=>simp only [List.map_cons,List.sum_cons,ih];ring

def maskedPacketsAt (Z : SeriesA G) (B : BudgetPoint) (σ C θ c : ℝ) (x : Site n) (U : Config G n):ℝ:=
  (Z.map fun a=>c^(a.grade-a.rise)*maskedPrismAt a B σ C θ x U).sum

def maskRosterPrice (C : ℝ) (d : ℕ) : ℝ:=2^d*(Fintype.card Signed*(C*(2^(d+2)*2)))

theorem spring_mask_packets (R : Run G) (simple : G.Simple) (heat : Poetry R.family.path.levels) (q : ℕ) :
    ∀ᶠ j : ℕ in atTop,∀N,j≤N→∀per (σ C c : ℝ),0<σ→0≤C→|c|≤2→
      ∀ (d : ℕ) (Z : SeriesA G), Draw Z σ C→(∀a∈Z,0<a.grade)→(∀a∈Z,a.grade≤d)→
      ∀(B : BudgetPoint) (x : Site (R.family.side j per)),
      let θ:=(R.family.path.rep N per j).p.threshold
      let fee:=(625*(Fintype.card PlaqAxes:ℝ))*R.family.path.levels.clock.forcedAllowance j^q
      let A:=maskRosterPrice C d
      let f (U : Config G (R.family.side j per)):=maskedPacketsAt Z B σ C θ c x U-springPacketsAt Z c x U
      Measurable f ∧ (∀U,‖f U‖≤Z.length*A) ∧ (∫U,‖f U‖ ∂scene R.family.path N per j)
        ≤ Z.length*(A*(1+2*(d+2)+625+σ⁻¹)*fee) := by
  filter_upwards [spring_mask_at R simple heat q] with j paid N live per σ C c hs hc bound d Z draw low high B x θ fee A f
  let μ:=scene R.family.path N per j
  letI : IsProbabilityMeasure μ:=probability R.makes.wilson live
  let p (a : PrismA G):=c^(a.grade-a.rise)
  let dlt (a : PrismA G) U:=maskedPrismAt a B σ C θ x U-sitePacket a.cells x U
  let F (a : PrismA G) U:=p a*dlt a U
  have same : f=fun U=>(Z.map fun a=>F a U).sum := by
    funext U
    dsimp only [f,F,p,dlt,maskedPacketsAt,springPacketsAt]
    simp_rw [mul_sub]
    exact (map_sub ..).symm
  rw [same]
  apply list_mask μ F Z
  intro a ha
  have src:=paid N live per a σ C hs (low a ha) (draw.2 a ha) B x
  have r:a.rise≤d:=a.rankA.trans (high a ha)
  have power : |p a|≤2^d := by
    change |c^(a.grade-a.rise)|≤2^d
    rw [abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg _) bound _).trans
      (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _|>.trans (high a ha)))
  let c1:=(Fintype.card Signed:ℝ)*(C*(2^(a.rise+2)*2))
  have cap : |p a| *c1≤A := by
    dsimp only [c1,A,maskRosterPrice]
    apply mul_le_mul power _ (by positivity) (by positivity)
    gcongr
    norm_num
  have a0 : 0≤A:=by dsimp only [A,maskRosterPrice];positivity
  have shape : (1+2*((a.rise:ℝ)+2)+625+σ⁻¹)≤1+2*((d:ℝ)+2)+625+σ⁻¹:=by gcongr
  have fe : 0≤fee:=mul_nonneg (by positivity) (pow_nonneg (Real.exp_pos _).le _)
  refine ⟨measurable_const.mul src.1,?_,?_⟩
  · intro U
    change ‖p a*dlt a U‖≤_
    rw [norm_mul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (src.2.1 U) (abs_nonneg _)).trans cap
  have equal (U) : ‖F a U‖=|p a| *‖dlt a U‖:=norm_mul _ _
  simp_rw [equal]
  rw [integral_const_mul]
  apply (mul_le_mul_of_nonneg_left src.2.2 (abs_nonneg _)).trans
  calc
    _ = (|p a| *c1)*(1+2*((a.rise:ℝ)+2)+625+σ⁻¹)*fee:=by dsimp only [c1];ring
    _ ≤ A*(1+2*((d:ℝ)+2)+625+σ⁻¹)*fee:=by gcongr

end YM.Integration.OriginalMarkedRunAction
