import YM.Integration.WilsonNeutralTwoPrintPathBoxMean

/-! A common finite relative-position truncation gives an actual cofinal
complex value, before the physical period limit. Each enhanced-period error
is sent to zero with the relative box held fixed. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonNeutralTwoPrintPathBoxLimit
open Filter Function Finset Lattice Wilson RG
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Mer
open WilsonCoeffUV.Soil WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Bank.Mosaic
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonNeutralTwoPrintPathBoxPlacement (box)
open WilsonNeutralTwoPrintPathBoxSweep (retained)
open WilsonNeutralTwoPrintPathBoxMean (plotted)
open WilsonNeutralTwoPrintPathPageLedger (price)
open WilsonNeutralTwoPrintPathRankFare (tariff)
open WilsonOriginalCensusDeckMean (mean)
open scoped Classical BigOperators Topology

theorem converges {B:Type}{l:Filter B}[l.NeBot](A:B→ℂ)(Z:ℕ→ℂ)(tail:ℕ→ℝ)
    (vanish:Tendsto tail atTop (𝓝 0))
    (fitted:∀D:ℕ,∀ε:ℝ,0<ε → ∀ᶠc in l,‖A c-Z D‖<tail D+ε):
    ∃z:ℂ,Tendsto A l (𝓝 z) ∧ Tendsto Z atTop (𝓝 z):=by
  have compact:CauchySeq Z:=by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨D,ready⟩:=eventually_atTop.1 (vanish.eventually_lt_const (show 0<ε/6 by positivity))
    refine ⟨D,?_⟩
    intro i hi j hj
    obtain ⟨c,first,second⟩:=((fitted i (ε/6) (by positivity)).and (fitted j (ε/6) (by positivity))).exists
    have gap:=dist_triangle (Z i) (A c) (Z j)
    rw [dist_comm (Z i) (A c),dist_eq_norm,dist_eq_norm,dist_eq_norm] at gap
    rw [dist_eq_norm]
    linarith [ready i hi,ready j hj]
  obtain ⟨z,complete⟩:=cauchySeq_tendsto_of_complete compact
  refine ⟨z,Metric.tendsto_nhds.mpr ?_,complete⟩
  intro ε hε
  obtain ⟨D,outside,inside⟩:=((vanish.eventually_lt_const (show 0<ε/3 by positivity)).and
    (Metric.tendsto_nhds.mp complete (ε/3) (by positivity))).exists
  filter_upwards [fitted D (ε/3) (by positivity)] with c paid
  have gap:=dist_triangle (A c) (Z D) z
  rw [dist_eq_norm (A c) (Z D)] at gap
  linarith

variable {I α V B:Type}[DecidableEq I][Fintype α][NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]
  {r:ℕ}{n:Side}{l:Filter B}[l.NeBot]

theorem original (X:B→Side)(grows:Tendsto (fun c=>(X c).val) l atTop)(h:∀c,n.val∣(X c).val)
    (S:Finset I)(o:I)(live:o∈S)(origin:Cover)(base:(S.erase o) → Cover)
    (root:(c:B)→Site (X c))(site:(c:B)→(S.erase o)→Site (X c))(center:∀c,splitter (h c) (root c)=wrap n origin)
    (addresses:∀c i,splitter (h c) (site c i)=wrap n (origin+base i))
    (P:(c:B)→(I → Cover)→Ten V (Site (X c) × α) r)(F:(I → Cover)→Ten V (Cloth α) r)(σ A:ℝ)(hs:0<σ)
    (paid:∀c y,MarkU y S (P c y) (F y) σ A)
    (motion:∀(v:Cover)(y:I → Cover),wrap n v=0 → plume (F (fun i=>v+y i)) n=plume (F y) n)
    (test:V →L[ℝ] ℂ)(weights:(Fin r→Site n × α)→ℂ)(height:ℝ)(hh:0≤height)(bounded:∀x,‖weights x‖ ≤ height):
    ∃z:ℂ,Tendsto (fun c=>mean (h c) (plotted (h c) S o (root c) (site c) (P c) test weights)) l (𝓝 z) ∧
    Tendsto (fun D=>retained n S o origin base D F test weights) atTop (𝓝 z):=by
  let tail:=fun D:ℕ=>(Real.exp (-((σ/2)/2)*(D:ℝ))*price S o α r σ (‖test‖*A))*height
  have growing:Tendsto (fun D:ℕ=>((σ/2)/2)*(D:ℝ)) atTop atTop:=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  have vanishes:Tendsto tail atTop (𝓝 0):=by
    have decay:=Real.tendsto_exp_neg_atTop_nhds_zero.comp growing
    simpa only [tail,Function.comp_apply,neg_mul,zero_mul] using (decay.mul_const
      (price S o α r σ (‖test‖*A))).mul_const height
  apply converges _ _ tail vanishes
  intro D ε hε
  have close:=(WilsonNeutralTwoPrintPathCofinalPeg.disappears σ
    ((box n base D).card*(‖test‖*height*tariff α r σ A)) hs).comp grows
  filter_upwards [grows.eventually (eventually_gt_atTop (32*D)),close.eventually_lt_const hε] with c room small
  exact (WilsonNeutralTwoPrintPathBoxMean.original (h c) S o live origin base (root c) (site c) (center c)
    (addresses c) D room (P c) F σ A hs (paid c) motion test weights height hh bounded).trans_lt
    (add_lt_add_right small _)

end YM.Integration.WilsonNeutralTwoPrintPathBoxLimit
end
