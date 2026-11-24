import YM.Integration.QLocalFullSupportPlot
import YM.RGLocalTaylor.Laminate.Gallery

/-! An authentic full support reserve funds the marked nonlinear step at a
    chosen input radius. Its change on every word is recorded explicitly. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalFullRootedOffer
open Function Filter Lattice Wilson RG Tree Precision Marker Finset
open Pressure Pressure.Tube Push Push.SectorMeasure Push.AbsoluteSums Push.GridApprox.Nil
open ConnectedActivityE6 Blaze Blaze.March PhysicalNext PhysicalNext.Repeat Lotus Daisy
open Merge MergeProof Menu RGLocalTaylor Laminate
open scoped Classical BigOperators

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P : Teller G} {T : Tube G S}
    {R : Rep G f} {W μ x C : ℝ} {Q : ConnectedActivityE6.Target G P}
    {o : Target.Order G W} (Y : Cash W x μ L Q o C T R)
    {ι V : Type} [Fintype ι] [Fintype V] [DecidableEq V] {Γ : Marker.Census V}
    (Z : V→Site f) (w : V→ℝ) (hw : ∀ i,0<w i) (rows : ι→Menu.Hat Γ R)
    {u a : ℝ} {k : ℕ}

include hw in
theorem plotted (ha : 0≤a) (hu : 0≤u) (foam : Daisy.foam Q L) (block : R.p.B≤2*radiusB x)
    (exponent : 4≤Q.relative) (offered : Menu.Offer Z rows w R.p.B R.p.supportExponent u)
    (occ : Extra.Multi.Occupancy (S.ratio.parent ∘ Z) k)
    (bought : Palette.shipPrice L Q x k (a*u)) :
    Palette.Plot (fun i=>(rows i).M) Y (fun i=>a*Menu.sumFee (rows i) w) := by
  have norm : 4*Q.ε<R.p.supportExponent := Y.laws.intake.exponent ▸ Q.grants.1
  have paid : (13/4:ℝ)*Q.ε≤R.p.supportExponent := by linarith [Q.usable]
  let leaves i := (rows i).M
  let owed i := a*Menu.sumFee (rows i) w
  have sites i j (hj : j∈(rows i).s.val) : Z j∈(leaves i).crest :=
    offered.sites i (Finset.mem_image_of_mem Z hj)
  refine Palette.FullRooted.acquired leaves Y owed (fun i=>mul_nonneg ha (Menu.timed _ hw)) Z
    (fun i=>(rows i).s.val) occ (fun i _=>?_) exponent paid foam block (mul_nonneg ha hu) ?_ bought
  · obtain ⟨j,hj⟩ := (rows i).shiny
    exact ⟨j,hj,sites i j hj⟩
  intro j
  have hs := budget_scale ha (offered.budget (Z j))
  refine Extra.Multi.Budget.mono hs (fun i=>?_) (fun i=>?_) le_rfl
  · split
    · exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (mul_nonneg ha (Menu.timed _ hw)) (leaves _).profit)
    exact le_rfl
  split
  next hi =>
    rw [if_pos (sites i j hi)]
    unfold Palette.wages Menu.fare owed leaves
    apply le_of_eq
    ring
  exact hs.1 i

include hw in
theorem month (hu : 0≤u) (foam : Daisy.foam Q L) (block : R.p.B≤2*radiusB x)
    (exponent : 4≤Q.relative) (offered : Menu.Offer Z rows w R.p.B R.p.supportExponent u)
    (occ : Extra.Multi.Occupancy (S.ratio.parent ∘ Z) k)
    (bought : Palette.shipPrice L Q x k u) :
    Laminate.Month (fun i=>(rows i).M) (fun i=>Menu.sumFee (rows i) w) (S.ratio.parent ∘ Z)
      (fun i=>Menu.sing (rows i) w) w Y := by
  have plot := plotted Y Z w hw rows (a:=1) zero_le_one hu foam block exponent offered occ
    (show Palette.shipPrice L Q x k (1*u) from (one_mul u).symm ▸ bought)
  refine ⟨fun i=>(Menu.virtue _ _).1,fun i=>(Menu.virtue _ _).2,?_,
    by simpa only [one_mul] using plot,hw,fun i=>Menu.paid (rows i) hw⟩
  intro i
  have covered : (rows i).s.val.image (S.ratio.parent ∘ Z) ⊆
      (rows i).M.crest.image S.ratio.parent := by
    intro z hz
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image_of_mem _ (offered.sites i (Finset.mem_image_of_mem Z hj))
  exact scope_send _ _ _ ((Accent.room _ _ _).2 covered)

omit [Fintype V] [Fintype ι] in
theorem word (v : Γ.Mode) (scale : ℝ) :
    Poly.toll (fun j=>scale*w j) v=scale^v.val.card*Poly.toll w v := by
  unfold Poly.toll
  rw [Finset.prod_mul_distrib,Finset.prod_const]

omit [Fintype V] [Fintype ι] in
theorem fare (h : Menu.Hat Γ R) (scale : ℝ) :
    Menu.fare h (fun j=>scale*w j)=scale^h.s.val.card*Menu.fare h w := by
  unfold Menu.fare Menu.sumFee
  rw [word w]
  ring

omit [Fintype V] [Fintype ι] in
private theorem first_power (h : Menu.Hat Γ R) {scale : ℝ} (pos : 0 ≤ scale) (upper : scale ≤ 1) :
    scale^h.s.val.card ≤ scale := by
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_pos.mpr h.shiny).ne'
  rw [hn,pow_succ]
  exact (mul_le_mul_of_nonneg_right (pow_le_one₀ pos upper) pos).trans_eq (one_mul _)

include hw in
omit [Fintype V] [Fintype ι] in
theorem scaled {δ : ℝ} (pos : 0<δ) (upper : δ≤1) (e : ℝ) (b : ℕ)
    (offered : Menu.Offer Z rows w b e u) : Menu.Offer Z rows (fun j=>δ*w j) b e (δ*u) := by
  refine ⟨offered.sites,fun z=>?_⟩
  have old := budget_scale pos.le (offered.budget z)
  refine Extra.Multi.Budget.mono old (fun i=>?_) (fun i=>?_) le_rfl
  · split
    · exact mul_nonneg (Menu.Crew _ (fun j=>mul_pos pos (hw j))) (Real.exp_pos _).le
    exact le_rfl
  by_cases h : z∈(rows i).M.crest
  · simp only [if_pos h,QLocalFullRootedOffer.fare w (rows i) δ]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (first_power _ pos.le upper)
      (Menu.Crew w hw)) (Real.exp_pos _).le).trans_eq (mul_assoc ..)
  simp [h]

def radius (limit amount : ℝ) := min 1 (limit/(1+|amount|))

include hw in
omit [Fintype V] [Fintype ι] in
theorem limited (limit : ℝ) (positive : 0<limit) (e : ℝ) (b : ℕ) (offered : Menu.Offer Z rows w b e u) :
    0<radius limit u ∧ radius limit u≤1 ∧
    Menu.Offer Z rows (fun j=>radius limit u*w j) b e limit := by
  have d : 0<1+|u| := by positivity
  have pos : 0<radius limit u := lt_min zero_lt_one (div_pos positive d)
  have top : radius limit u≤1 := min_le_left _ _
  have mul : radius limit u*u≤limit := calc
    _ ≤ radius limit u*(1+|u|) := mul_le_mul_of_nonneg_left (by linarith [le_abs_self u]) pos.le
    _ ≤ (limit/(1+|u|))*(1+|u|) := mul_le_mul_of_nonneg_right (min_le_right _ _) d.le
    _ = limit := div_mul_cancel₀ _ d.ne'
  have small := scaled Z w hw rows pos top e b offered
  exact ⟨pos,top,⟨small.sites,fun z=>budget_loosen (small.budget z) mul⟩⟩

end YM.Integration.QLocalFullRootedOffer
end
