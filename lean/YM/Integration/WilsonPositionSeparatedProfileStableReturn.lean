import YM.Integration.WilsonPositionSeparatedProfileStableStep

/-! The original scalar report of a freshly grouped source. Removal of each
primary commutes with its genuine Wilson transport and the geometric bills
pay all scalar coefficients emitted below the capture. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileStableReturn
open Function MeasureTheory Filter Lattice Wilson RG Source Labels Extra.Histories
open RG05Readout Address Native Push.GridApprox ProjectorNext.Equivariance Trace.Physical
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage
open WilsonPositionSeparatedProfileStableStep
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G)

private theorem vacuum_step {N per i : ℕ} (live : i < N)
    (f : Config G (R.family.side (i+1) per) → ℂ) (hf : Integrable f (prior G _)) (c : ℂ) :
    let H:=R.family.path
    (H.levels.clock.op i per).push (H.β N per (i+1)) (f+c • liftVac H N per (i+1)) =
      (H.levels.clock.op i per).push (H.β N per (i+1)) f+c • liftVac H N per i := by
  let H:=R.family.path
  let v:=liftVac H N per (i+1)
  have h : Integrable v (prior G _) := vac_integrable H N per (i+1) R.makes.wilson live
  dsimp only
  rw [StepData.push_add (H.levels.transition_mass ..) f (c • v) hf (h.smul c),StepData.push_smul _ _ _ _ h,
    ←vac_transfer H N per i R.makes.wilson live]

private theorem affine {u b N per : ℕ} (age : u ≤ b) (cut : b ≤ N)
    (f : Config G (R.family.side b per) → ℂ) (hf : Integrable f (prior G _)) (c : ℂ) :
    let H:=R.family.path
    pushTo H N per age (f+c • liftVac H N per b)=pushTo H N per age f+c • liftVac H N per u := by
  dsimp only
  induction b,age using Nat.le_induction with
  | base=>simp
  | succ i hi ih=>
    rw [pushTo_next R.family.path N per hi,pushTo_next R.family.path N per hi,vacuum_step R cut f hf]
    exact ih (Nat.le_trans i.le_succ cut) _ (StepData.push_integrable (R.family.path.levels.transition_mass ..) _ hf)

def read {u b N per : ℕ} (age : u ≤ b) (X : Coefficient (R.family.labels.level 0) (R.family.side b per)) : ℂ :=
  pushTo R.family.path N per age (X.density 0 (R.family.localSection 0) (R.family.path.rep N per b)) 1 /
    liftVac R.family.path N per u 1

private theorem vac_ne (u N per : ℕ) : liftVac R.family.path N per u 1 ≠ 0 := by
  let A:=R.family.path.rep N per u
  have empty:RG.flags A.p.threshold (1:Config G (R.family.side u per))=∅ :=
    (offFlags _ A.p.threshold_pos).self_of_nhds
  exact noFlagEval (R:=A) empty

theorem station {b N per : ℕ} (X : Coefficient (R.family.labels.level 0) (R.family.side b per))
    (form : X.Format 0 R.family.params (R.family.path.rep N per b)) :
    read (N:=N) R (u:=b) le_rfl X = X.x 0 := by
  rw [read,pushTo_self]
  apply (div_eq_iff (vac_ne R b N per)).mpr
  exact (WilsonPositionSeparatedProfileFlatField.vacuum (R.family.localSection 0) (R.makes.sections 0) _ 0 X form).trans (mul_comm ..)

theorem emission {u i N per : ℕ} (age : u ≤ i) (live : i < N)
    (X : Coefficient (R.family.labels.level 0) (R.family.side (i+1) per))
    (Y : Coefficient (R.family.labels.level 0) (R.family.side i per)) {w : ℝ}
    (form : X.Format 0 R.family.params (R.family.path.rep N per (i+1)))
    (cash : X.remBound 0 (R.family.path.rep N per (i+1)) (Real.sqrt (R.family.path.levels.clock.forcedAllowance (i+1))) w)
    (step : Y.density 0 (R.family.localSection 0) (R.family.path.rep N per i) = blast R.family.path N per i 0
      ((strip X).density 0 (R.family.localSection 0) (R.family.path.rep N per (i+1)))) :
    read (N:=N) R (age.trans i.le_succ) X=read (N:=N) R age Y + X.x 0 := by
  let H:=R.family.path
  let S:=R.family.localSection 0
  let A:=H.rep N per
  let f:=(strip X).density 0 S (A (i+1))
  have cutForm : (strip X).Format 0 R.family.params (A (i+1)):=
    ⟨form.smooth,form.origin,form.identity_null,form.projects,form.forcing,form.carried,form.invariant,form.supported,form.borel⟩
  have hf:Integrable f (prior G _):=play_integrable H _ R.makes.wilson live cutForm cash
  have whole:X.density 0 S (A (i+1))=f+(X.x 0) • liftVac H N per (i+1):=by
    funext V
    change X.density 0 S (A (i+1)) V=(strip X).density 0 S (A (i+1)) V+(X.x 0)*((A (i+1)).eval V:ℂ)
    rw [WilsonPositionSeparatedProfileStableStep.density]; ring
  have eqY:(H.levels.clock.op i per).push (H.β N per (i+1)) f=Y.density 0 S (A i):=by
    simpa only [blast,pow_zero,one_smul] using step.symm
  have hy:Integrable (Y.density 0 S (A i)) (prior G _):=eqY ▸ StepData.push_integrable (H.levels.transition_mass ..) f hf
  unfold read
  rw [whole,pushTo_next H N per age,vacuum_step R live f hf,eqY,affine R age live.le _ hy]
  rw [Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_div,mul_div_cancel_right₀ _ (vac_ne R u N per)]

noncomputable def price : ℝ := shrink/(1-shrink)

private theorem price_pos : 0 ≤ price := div_nonneg shrink_pos.le (sub_pos.mpr shrink_lt).le

private theorem price_next : (price+1)*shrink=price := by
  unfold price
  field_simp [(sub_pos.mpr shrink_lt).ne']
  ring

theorem original (D : OPE.Package R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors)
    {u b N per : ℕ} (grade : R.family.ref 0 ≤ u) (age : u ≤ b) (cut : b ≤ N)
    (X : Coefficient (R.family.labels.level 0) (R.family.side b per)) {w : ℝ}
    (form : X.Format 0 R.family.params (R.family.path.rep N per b))
    (cash : X.remBound 0 (R.family.path.rep N per b) (Real.sqrt (R.family.path.levels.clock.forcedAllowance b)) w) :
    ‖read (N:=N) R age X-X.x 0‖ ≤ price*w := by
  induction b,age using Nat.le_induction generalizing w with
  | base =>
    rw [station R X form,sub_self,norm_zero]
    obtain ⟨a,c,ha,hc,h,_⟩:=cash
    exact mul_nonneg price_pos ((add_nonneg ha hc).trans h)
  | succ i hi ih =>
    obtain ⟨Y,a,_,a_small,_,fy,cy,yp,step⟩:=issued R D (grade.trans hi) cut X form cash
    have last:=ih (i.le_succ.trans cut) Y fy cy
    rw [emission R hi cut X Y form cash step,add_sub_cancel_right]
    calc
      ‖read (N:=N) R hi Y‖ ≤ ‖read (N:=N) R hi Y-Y.x 0‖+‖Y.x 0‖:=by
        simpa only [sub_add_cancel] using norm_add_le (read (N:=N) R hi Y-Y.x 0) (Y.x 0)
      _ ≤ price*a+a := add_le_add last yp
      _ = (price+1)*a:=by ring
      _ ≤ (price+1)*(shrink*w):=mul_le_mul_of_nonneg_left a_small (by linarith [price_pos])
      _ = price*w:=by rw [←mul_assoc,price_next]

end YM.Integration.WilsonPositionSeparatedProfileStableReturn
