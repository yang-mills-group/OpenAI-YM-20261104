import YM.Integration.WilsonReflectedPhysicalFiling
import YM.Integration.WilsonMacroscopicRichChildRegistration
import YM.RG16.Unmasked.Merits

/-! The literal earlier filed counterterm, in its own cutoff coordinates,
on the fixed physical chamber. The constant precedes both regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReflectedPhysicalCounterterm
open Filter Function Lattice Wilson RG OPE OPE.Log Trace.Pilot MergeProof
open Cells Stock Extra.Histories PhysicalNext.Repeat.Legato Bid Bandage Push RG16.Literal
open MergeProof.Ribbons MergeProof.Accent
open Trace.Physical.GermGraph WilsonReflectedPhysicalRate
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G)
variable (book:OPE.Package R.family R.w (mutt R.alloy.B.a R.Q) R.doors)

include book in
theorem original (h J u:ℕ) (enlarged:R.family.ref h ≤ J)
    (station:∀p,Opened R.family h u p) (tiling:Stock.Tabs.opens R.family.path.levels 1 J u)
    {E:ℝ→ℝ} (capital:RateIs trail LogV E (-(h:ℝ))) :
    ∃ K≥1,∀ᶠ r in trail,let b:=capture R r
      ∀(N p:ℕ) (ub:u ≤ b) (bn:b ≤ N) (Y:Cut R.family N p) (q:store R.family h p b)
        (x:R.family.label h) (dR:ℝ),
      Funds R.family R.makes p N b h J u (E r) dR (Real.exp (((h:ℝ)+1/16)*LogV r))
        Y tiling.1 ub bn (station p) x q →
      let filed:=WilsonMacroscopicRichChildRegistration.returned R.family R.makes (station p) (ub.trans bn) Y
      let Q:=Y-R.family.O N p filed 0
      let M:=center R.family.S p (tiling.1.trans (ub.trans bn)) 0
      Interior (M.chamber 0) Q ∧ M.rootTest (R.family.beta N p) Q ≤ K*r^((h:ℝ)+1/32) :=by
  obtain ⟨C,cp,columns⟩:=cylinder_cost R.family book R.makes h J u tiling enlarged station
  let K:=max 1 C
  have one:1 ≤ K:=le_max_left ..
  have coef:C ≤ K:=le_max_right ..
  have kp:0≤K:=zero_le_one.trans one
  have cap:Height R.family.S trail LogV (capture R) 1:=
    Log.previous PhysMS.to_log_zoom (WilsonCloseCaptureDate.height R) R.family.path.levels.fits.mesh
  obtain ⟨n,near⟩:=eventually_atTop.mp (near_center R.family J h R.makes)
  refine ⟨K,one,?_⟩
  filter_upwards [physical R u h capital (stakes R.family J u),cap.grows.eventually_ge_atTop n,
    cap.grows.eventually_gt_atTop u,capital.pos,self_mem_nhdsWithin] with r estimated enough live epos rp
  intro b N p ub bn Y q x dR paid
  let w:=Real.exp (((h:ℝ)+1/16)*LogV r)
  let a:=2*(stakes R.family J u/w)
  let c:=E r/gainChart R.family.path b u
  have ap:0 ≤ a:=by unfold a stakes w; positivity
  have gp:0 < gainChart R.family.path b u:=Real.exp_pos _
  have bp:0 ≤ c:=(div_pos epos gp).le
  have converted : Real.exp ((-(h:ℝ)-1/32)*LogV r)=r^((h:ℝ)+1/32):=by
    rw [Real.rpow_def_of_pos rp]
    unfold LogV
    rw [Real.log_inv];congr 1;ring
  have price:a+c ≤ r^((h:ℝ)+1/32):=estimated.trans_eq converted
  have original:=Funds.pay R.family R.makes p N b h J u paid cp (fun y=>⟨near N (enough.trans bn)
    (tiling.1.trans (ub.trans bn)) p 0 (by rw [latzero];simp [(R.family.S.a_pos J).le]) y,
    columns N p (live.trans_le bn) y⟩)
  refine ⟨original.1,original.2.trans ?_⟩
  change a+C*c ≤ K*r^((h:ℝ)+1/32)
  calc
    a+C*c ≤ K*a+K*c:=add_le_add (by simpa only [one_mul] using mul_le_mul_of_nonneg_right one ap)
      (mul_le_mul_of_nonneg_right coef bp)
    _ = K*(a+c):=(mul_add ..).symm
    _ ≤ _:=mul_le_mul_of_nonneg_left price kp
end YM.Integration.WilsonReflectedPhysicalCounterterm
