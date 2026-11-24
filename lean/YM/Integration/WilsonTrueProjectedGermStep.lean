import YM.Integration.WilsonTrueProjectedColumnStep

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedGermStep
open Filter MeasureTheory Lattice Wilson RG Source Labels
open Trace.Physical Trace.Physical.GermGraph PhysicalNext.Repeat.Legato
open Extra.Histories Extra.Histories.Relay Bid MergeProof
open scoped Topology Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {d N p i : ℕ}
local notation "σ" => (C.labels.level d).coeffSize
local notation "Q" => GermGraph.store C d p
local notation "V" => GermGraph.value (C:=C) d N p
local notation "Y" => GermGraph.calValues (C:=C) d N p
local notation "π" => GermGraph.page (C:=C) d p
local notation "X" => GermGraph.measuring C d N p
local notation "U" => GermGraph.transition (C:=C) d N p i
local notation "L" => GermGraph.factor C i

/-- The proposed fields can be any literal functions on the original Wilson
configurations. Only the observed lower germ needs a canonical template.
This lets the original hard histories stay with their own vacuum. -/
theorem original (H : C.Makes) (hi : i < N) (hc : Opened C d i p)
    {γ ε r b m : ℝ} (gate : Gate C d N p i γ ε)
    (y : C.label d) (fine : Config G (C.side (i+1) p) → ℂ) (q : Q (i+1))
    (model : Config G (C.side i p) → ℂ) (coarse e : Q i)
    (hq : reads d N p (i+1) q r) (null : π (i+1) q = 0)
    (input : Y (i+1) y = fine + V (i+1) q)
    (measured : reads d N p i coarse m) (funded : reads d N p i e b)
    (germ : model =ᶠ[𝓝 1] V i coarse)
    (defect : U fine = model + V i e) :
    let loss := L ^ (-GermGraph.rate)
    let fit := fitting d N p i H hc hi.le
    ∃ (s : Q i) (z : C.label d),
      reads d N p i s (loss*r + (b + (2*stock C i)*σ (π i e))) ∧ π i s = 0 ∧
      σ (X i z) ≤ ε*r*loss ∧ X i y - π i coarse = X i z + π i e ∧
      V i s = Y i (fit.symm (π i coarse)) - model := by
  intro loss fit
  obtain ⟨v,z,hv,hv0,hz,pushed⟩ := gate.2 q r hq null
  obtain ⟨w,t,hw,hw0,splitE,xt⟩ := fresh_split0 H hc hi.le e funded
  let s := beside v w
  have hs : reads d N p i s (loss*r + (b + (2*stock C i)*σ (π i e))) :=
    presentation hv.1 hv.2 hw.1 hw.2
  have hs0 : π i s = 0 := by
    rw [show s = beside v w from rfl,addPage d N p i v w H hc.post hi.le hv hw,hv0,hw0,add_zero]
  have sv : V i s = V i v + V i w := plus (H.wilson.represents N p i hi.le).good
    hv.2 hw.2 (C.localSection d)
  have lower : reads d N p i (beside coarse s) (m+_) := presentation measured.1 measured.2 hs.1 hs.2
  have lower_val : V i (beside coarse s) = V i coarse + V i s :=
    plus (H.wilson.represents N p i hi.le).good measured.2 hs.2 (C.localSection d)
  have qi := message d N p (i+1) H (hc.post.trans i.le_succ) hi hq
  have yi := message d N p (i+1) H (hc.post.trans i.le_succ) hi
    (entryOk d N p (i+1) H (hc.post.trans i.le_succ) hi y)
  have fi : Integrable fine (prior G _) := by
    rw [show fine = Y (i+1) y - V (i+1) q by rw [input]; abel]
    exact yi.sub qi
  have field : Y i y = (model + V i s) + Y i (z+t) := by
    rw [factory_eq d N p i H hc.post hi y,input,transition_add d N p fi qi,defect,pushed,splitE,
      sv,cal_add d N p i H hc.post hi.le]
    abel
  have neg : Y i (-(z+t)) = -Y i (z+t) := by
    have h := negative_cal H hc hi.le (z+t)
    exact eq_neg_of_add_eq_zero_left h
  have matched : Y i (y-(z+t)) = model + V i s := by
    rw [sub_eq_add_neg,cal_add d N p i H hc.post hi.le,neg,field]
    abel
  have near : Y i (y-(z+t)) =ᶠ[𝓝 1] V i (beside coarse s) := by
    rw [matched,lower_val]
    exact germ.add (Filter.EventuallyEq.rfl)
  have coord := same_page H hi.le hc.post (entryOk d N p i H hc.post hi.le (y-(z+t))) lower
    near
  change fit (y-(z+t)) = π i (beside coarse s) at coord
  rw [addPage d N p i coarse s H hc.post hi.le measured hs,hs0,add_zero] at coord
  have feed : X i y - π i coarse = X i z + π i e := by
    change fit y - π i coarse = fit z + π i e
    rw [←xt,←coord,map_sub,map_add]
    abel
  have gain : 0 < L^GermGraph.rate := Real.rpow_pos_of_pos
    (zero_lt_one.trans (factor_positive C i)) _
  have bill : σ (X i z) ≤ ε*r*loss := by
    rw [show loss = (L^GermGraph.rate)⁻¹ from
      Real.rpow_neg (zero_lt_one.trans (factor_positive C i)).le _,←div_eq_mul_inv]
    exact (le_div_iff₀ gain).mpr (by simpa only [mul_comm (σ (X i z))] using hz)
  refine ⟨s,z,hs,hs0,bill,feed,?_⟩
  rw [←coord,LinearEquiv.symm_apply_apply,matched]
  abel

end YM.Integration.WilsonTrueProjectedGermStep
