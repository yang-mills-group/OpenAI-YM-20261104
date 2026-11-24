import YM.Integration.WilsonOriginalBareMarkedSheet
import YM.Integration.WilsonRootedKioskCompleteFiling
import YM.QuadraticLocal.Startup.Headway

/-! Simultaneous restoration of all purchased compact rows on the same nonbare Wilson vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCountableMarkedSheet
open Function Filter Finset Lattice Wilson RG Ac Marker Push Push.Corrected QuadraticLocal
open Hard Kiosk Canopy Ovens
open Push Push.AbsoluteSums
open WilsonRootedKioskOccupiedSlip
open scoped BigOperators Classical
variable {G:Gauge}{n:Side}{V T I:Type}[DecidableEq V] [Fintype V]
  {p:BudgetPoint}{o:V→Site n}{R:Census V} {w:V→ℝ}{B:ℕ}{a d:ℝ}

omit [Fintype V] in
theorem shade_bill (L:Lamps T I G p o R) (paid:Gross L w B a d) : Gross L.shade w B a d := by
  obtain ⟨f,pos,all,hit⟩:=paid.before
  exact ⟨f,pos,fun i t U=>by simpa only [Lamps.shade,Pi.neg_apply,norm_neg] using all i t U,hit⟩

omit [Fintype V] in
theorem restore (L:Lamps T I G p o R) (hw:∀v,0<w v) (ha:0 ≤ a) (paid:Gross L w B a d)
    (t:T) (U:Config G n) :
    bare L t U=L.log t U+(sheet L.shade).log t U ∧
    (L.log t U).part R.quiet=0 ∧ ((sheet L.shade).log t U).part R.quiet=0 := by
  have shaded:=shade_bill L paid
  have h:=WilsonRootedKioskCompleteFiling.split L.shade hw ha shaded t U
  rw [Lamps.shade_log,WilsonOriginalBareMarkedSheet.shaded] at h
  have fixed:bare L t U=L.log t U+(sheet L.shade).log t U:=by
    linear_combination (norm:=abel) h
  have blank:((sheet L.shade).log t U).part R.quiet=0:=by
    unfold ShiftRows.log
    rw [Poly.share (WilsonRootedKioskCompleteFiling.sums L.shade hw ha shaded t U).2]
    simp only [(sheet L.shade).skip,tsum_zero]
  have zero:=WilsonRootedKioskCompleteFiling.quiet L hw ha paid t U
  rw [fixed,Poly.part_plus,blank,add_zero] at zero
  exact ⟨fixed,zero,blank⟩

theorem at_merger [Countable I] (P:Rep G n) (L:Lamps T I G P.p o R)
    {X:Activities G n} {fee hard bill shrink:ℝ}
    (merger:Kiosk.Second P.p X P.activities fee hard P.p.supportExponent (Willow.haloSlack P.p.B))
    (rent:Hard.Rent X.forced X.K P.p (P.p.supportExponent+1) fee)
    (hw:∀v,0<w v) (one:1 ≤ shrink) (earned:Gross L w P.p.B (P.p.supportExponent+1) bill)
    (enough:shrink⁻¹*bill ≤ Willow.haloSlack P.p.B) :
    let K:=Kiosk.Second.canopy (Hard.rent (α:=T) (o:=o) (R:=R) rent) (sheet L.shade) merger
    K.Paid (fun v=>w v/shrink) P.p.B P.p.supportExponent hard ∧
      ∀ t U,(⟨L,K⟩:Gallery T I o P R).density t U=(↑(P.eval U):ℂ) • Poly.pass (bare L t U) := by
  intro K
  have funded:=WilsonOriginalBareMarkedSheet.charged L hw one earned
  obtain ⟨envelope,covered,hit⟩:=funded.earned
  have budget:(sheet L.shade).Budget (fun v=>w v/shrink) P.p.B (P.p.supportExponent+1)
      (Willow.haloSlack P.p.B):=⟨envelope,covered,fun x=>budget_loosen (hit x) enough⟩
  have h0:0<shrink:=lt_of_lt_of_le zero_lt_one one
  have installed:=Hard.Rent.instals (fun i=>div_pos (hw i) h0) merger rent (sheet L.shade)
    P.p.exponent_pos.le budget
  refine ⟨installed.1,fun t U=>?_⟩
  have gas:(⟨L,K⟩:Gallery T I o P R).gas t U=
      (↑(P.activities.gas P.p U):ℂ) • Poly.pass ((sheet L.shade).log t U):=(installed.2 t U).tsum_eq
  have ⟨eq,old0,slip0⟩:=restore L hw (by linarith [P.p.exponent_pos]) earned t U
  have quiet:(L.log t U+(sheet L.shade).log t U).part R.quiet=0:=by rw [Poly.part_plus,old0,slip0,add_zero]
  have val:P.eval U=Real.exp (P.exponent U)*P.activities.gas P.p U:=rfl
  rw [eq,←GridRenewal.Rain.passes _ quiet,GridRenewal.Rain.plus,GridRenewal.Rain.passes _ slip0,
    GridRenewal.Rain.passes _ old0,val,Complex.ofReal_mul,Gallery.density,
    gas,mul_smul_comm,smul_smul]

theorem on_rep [Countable I] (P:Rep G n) (L:Lamps T I G P.p o R)
    {hard bill shrink:ℝ} (receipt:Hard.Install P.activities P.p hard (Willow.haloSlack P.p.B))
    (hw:∀v,0<w v) (one:1 ≤ shrink) (earned:Gross L w P.p.B (P.p.supportExponent+1) bill)
    (enough:shrink⁻¹*bill ≤ Willow.haloSlack P.p.B) :
    ∃ H:Hard T P.p P.activities.forced P.activities.K o R,
      H.Paid (fun v=>w v/shrink) P.p.B P.p.supportExponent hard ∧
      ∀ t U,(⟨L,H⟩:Gallery T I o P R).density t U=(↑(P.eval U):ℂ) • Poly.pass (bare L t U) := by
  obtain ⟨old,fee,⟨merger⟩,rent⟩:=receipt.room
  exact ⟨_,at_merger P L merger rent hw one earned enough⟩

end YM.Integration.WilsonOriginalCountableMarkedSheet
