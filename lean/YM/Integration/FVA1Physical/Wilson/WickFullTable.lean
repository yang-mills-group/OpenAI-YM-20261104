import YM.Integration.FVA1Physical.Wilson.WickMarkerAlgebra
import YM.Integration.FVA1Physical.Marked.ForecastCost

/-! True conditional expectation of an entire finite weighted marker bank,
including its nonlinear exponential and normalized connected logarithm. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Finset MeasureTheory Lattice RG Marker Comparison.RG02 Comparison.RG02.Valence Comparison.RG02.Order
open YM.Next.SectorChange YM.Extra.Trajectories SignCovariance
open scoped BigOperators Classical ContDiff
variable {I V:Type} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] {R:Census I}
local notation "Y" => (V→ℝ)
def wickEntries (K:Matrix V V ℝ) (f:Y→Poly R) :Poly R :=
  fun m=>∫ z,(f z).part m ∂Gaussian.cloud K

def wickTableRent (R:Census I) (d:ℕ) (C A:ℝ):ℝ:= Fintype.card R.Mode*(2*cubeWickPrice d C A)

variable (K:Matrix V V ℝ) (pd:K.PosDef) {C A:ℝ} (hc:0≤C) (rows:∀i,∑ j,|K i j|≤C) (ha:0<A)
variable (w:I→ℝ) (hw:∀i,0<w i)
include pd hc rows ha hw
omit [Fintype I] in
theorem wick_entries_price (d:ℕ) (f:Y→Poly R) (rank:TableDegree d f) {B:ℝ}
    (hit:∀ z,‖z‖≤A→Poly.price w (f z)≤B) :
    Poly.price w (wickEntries K f)≤wickTableRent R d C A*B := by
  let P:=2*cubeWickPrice d C A
  have price (m:R.Mode):Poly.toll w m*‖(wickEntries K f).part m‖≤P*B := by
    have hpos:=Poly.worth hw m
    have val:=complex_wick_cube K pd hc rows ha (rank m) (δ:=B/Poly.toll w m)
      (fun z hz=>(le_div_iff₀ hpos).2 (by rw [mul_comm];exact (Poly.member hw m (f z)).trans (hit z hz)))
    exact (mul_le_mul_of_nonneg_left val hpos.le).trans_eq (by dsimp only [P];field_simp)
  apply (sum_le_sum (s:=univ) fun m _=>price m).trans_eq
  rw [sum_const,card_univ,nsmul_eq_mul];unfold wickTableRent P;ring

omit [Fintype I] in
theorem wick_entries_error (d:ℕ) (f g:Y→Poly R) (hf:TableDegree d f)(hg:TableDegree d g) {δ:ℝ}
    (hit:∀z,‖z‖≤A→Poly.price w (f z-g z)≤δ) :
    Poly.price w (wickEntries K f-wickEntries K g)≤wickTableRent R d C A*δ := by
  have subrank:TableDegree d (fun z=>f z-g z) := by
    intro m;change Level (d:ℤ) (fun z=>(f z).part m-(g z).part m)
    simpa only [neg_one_mul,sub_eq_add_neg] using (hf m).add ((hg m).factor (-1))
  rw [show wickEntries K f-wickEntries K g=wickEntries K (fun z=>f z-g z) by
    ext m
    change (∫ z,(f z).part m ∂Gaussian.cloud K)-(∫ z,(g z).part m ∂Gaussian.cloud K)=_
    exact (integral_sub (finite_level_integrable K pd (hf m)) (finite_level_integrable K pd (hg m))).symm]
  exact wick_entries_price K pd hc rows ha w hw d _ subrank hit

def wickMoment (K:Matrix V V ℝ) (f:Y→Poly R):Poly R:=wickEntries K (fun z=>Poly.pass (f z))
def wickLogBill (R:Census I) (d:ℕ) (C A H:ℝ):ℝ:=
  let n:=Fintype.card I
  let P:=wickTableRent R (n*d) C A
  repeats n (1+P*repeats (n+1) H)*(P*passSlope n H)

theorem wick_log_difference (d:ℕ) (f g:Y→Poly R) (hf:TableDegree d f)(hg:TableDegree d g)
    (fz:∀z,(f z).part R.quiet=0) (gz:∀z,(g z).part R.quiet=0)
    {H δ:ℝ} (hp:0≤H) (sizes:∀z,‖z‖≤A→Poly.price w (f z)≤H ∧ Poly.price w (g z)≤H)
    (hit:∀z,‖z‖≤A→Poly.price w (f z-g z)≤δ) :
    Poly.price w (connected (wickMoment K f)-connected (wickMoment K g))≤wickLogBill R d C A H * δ := by
  let n:=Fintype.card I
  let P:=wickTableRent R (n*d) C A
  have pp:0≤P:=mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (cubeWick_nonnegative _ hc ha))
  have hK:=repeats_pos (n+1) H hp
  let μ:=Gaussian.cloud K
  haveI : IsProbabilityMeasure μ := inferInstanceAs (IsProbabilityMeasure (Gaussian.cloud K))
  have unit (a:Y→Poly R) (az:∀z,(a z).part R.quiet=0) : (wickMoment K a).part R.quiet=1 := by
    change (∫ z,(Poly.pass (a z)).part R.quiet ∂μ)=1
    simp_rw [Poly.pass_part _ (az _)];simp
  have mass (a:Y→Poly R) (rk:TableDegree d a) (upper:∀z,‖z‖≤A→Poly.price w (a z)≤H):
      Poly.price w (1-wickMoment K a)≤1+P*repeats (n+1) H := by
    apply (priced_sub w hw ..).trans
    rw [Poly.one_price];apply add_le_add le_rfl
    exact wick_entries_price K pd hc rows ha w hw _ _ (table_pass_degree rk)
      (fun z hz=>Marked.finite_pass_price hw (a z) (upper z hz))
  have δr:=wick_entries_error K pd hc rows ha w hw _ _ _ (table_pass_degree hf) (table_pass_degree hg)
    (δ:=passSlope n H*δ) (fun z hz=>(pass_difference w hw (f z) (g z) (sizes z hz).1 (sizes z hz).2).trans
      (mul_le_mul_of_nonneg_left (hit z hz) (passSlope_nonnegative n hp)))
  have h:=lip (wickMoment K f) (wickMoment K g) w hw (unit f fz) (unit g gz)
    (mass f hf (fun z hz=>(sizes z hz).1)) (mass g hg (fun z hz=>(sizes z hz).2))
    n (fun m=>card_le_univ _)
  exact (h.trans (mul_le_mul_of_nonneg_left δr
      (repeats_pos n _ (add_nonneg zero_le_one (mul_nonneg pp hK))))).trans_eq (by unfold wickLogBill;ring)
end YM.Integration.FVA1Physical.Wilson
