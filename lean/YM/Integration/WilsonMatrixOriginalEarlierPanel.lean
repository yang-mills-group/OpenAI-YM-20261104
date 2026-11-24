import YM.Integration.WilsonMatrixOriginalFiledPanel
import YM.Integration.WilsonInvariantActionSubmittedCapture

/-! The signed submitted Ward panel remains nonzero on the inherited, positive Wilson law. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonMatrixOriginalEarlierPanel
open Filter Function Set MeasureTheory Lattice Wilson RG RG17 Source Marker Extraction Extraction.Order
open Table Spec Climb Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS OPE OPE.Therm
open Next.UVStress Next.Rank.Price PhysicalNext.Repeat.Legato SharpGram.Lenses FVA2 FVA2.Register
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMatrixTicketLanesSmearedRows
open WilsonInvariantActionPairProbe WilsonInvariantActionSpectatorPrices WilsonInvariantActionPairCovariance
open WilsonLimitConstruction WilsonInvariantActionCalibratedColumn WilsonInvariantActionPosition
open WilsonMatrixOriginalFiledPanel WilsonInvariantActionCapturedProfile
open private packet_real from YM.Integration.WilsonMatrixOriginalFirstSignedPanel
open scoped Classical Topology BigOperators

private def orientation (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1
private theorem orientation_cases (x : ℝ) : orientation x=1 ∨ orientation x= -1 := by
  unfold orientation
  split <;> simp
private theorem orientation_abs (x : ℝ) : orientation x*x=|x| := by
  by_cases h : 0 ≤ x
  · simp [orientation,h,abs_of_nonneg h]
  · simp [orientation,h,abs_of_neg (lt_of_not_ge h)]
private theorem component (χ : ℂ →L[ℝ] ℝ) (choice : χ=Complex.reCLM ∨ χ=Complex.imCLM)
    (x y : ℂ) : |χ x-χ y| ≤ ‖x-y‖ := by
  rcases choice with rfl | rfl
  · exact Complex.abs_re_le_norm (x-y)
  · exact Complex.abs_im_le_norm (x-y)
private theorem sign_lower {σ x y d : ℝ} (choose : σ=1 ∨ σ= -1)
    (gap : 3*d/4 < σ*x) (near : |y-x| ≤ d/8) (hd : 0 < d) : d/2 < σ*y := by
  obtain ⟨a,b⟩ := abs_le.mp near
  rcases choose with rfl | rfl <;> simp only [one_mul,neg_one_mul] at * <;> linarith

variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (J:ℝ→tower S) (Z:WilsonPrescription G)
    {H:(Bel R.family.book).Hierarchy} (lead:Leading F J)
    (paid:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d) (simple:G.Simple)
    {ρ:ℝ} {T:Campaign R} {P:Campaign.Pillars R T} (funded:FundedOriginalProperties.{u} simple ρ P)
    (subsidy:WilsonReportColumnSubsidy.Eligible R.kit)
    (pace:WilsonWindowReportingPace.Slow R.kit) (L:Layout F)
    {B:ℕ} (hB:0<B) (level:L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B)
    {U:Filter (ℕ×ℕ)} [U.NeBot] (chosen:U ≤ L.lens)
    {u₀:Filter (ℕ×ℕ)} (bank:Mantle F u₀) (E:Services R.family f S) (pegs:Pegs bank L)
local notation "β" => R.family.path.levels.clock.hatBeta

def Row (δ g : ℝ → ℝ) (D:Profiles R 4) (j:D.probes.index) (v₀:(standard R.family.labels).Ref 4)
      (hs:D.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 v₀)
      (e:ℕ) (deposit:ℝ→RG17.Free R.family 4→R.family.label 4) (χ:ℂ→L[ℝ]ℝ) (σ:ℝ) : Prop :=
      let φ := WilsonInvariantActionCalibratedColumn.packet v₀ hs (test D j)
      let v := (Bel R.family.book).project 4 v₀
      let a := fun r => deposit r (stepField R.family)
      let b := fun r => deposit r (freeInput F J Z 4 r v)
      let cov := fun r=>tested (J r 4 (stepField R.family)) (homogeneous F J Z r 4 v) r φ
      let c := tree (D.probes.shell j) (test D j) H 4 (stepField R.family)
      (χ=Complex.reCLM ∨ χ=Complex.imCLM) ∧ (σ=1 ∨ σ= -1) ∧ σ*χ c=|χ c| ∧ 0< |χ c| ∧
      Tendsto cov trail (𝓝 c) ∧
      (∀ᶠ r in trail,let trace := tested (TraceExtension.center F) (homogeneous F J Z r 4 v) r φ
        trace ≠ 0 ∧ ((r^4/(4*δ r):ℝ):ℂ)=cov r / trace) ∧
      Filed (U:=U) F J L a b (fun r=>homogeneous F J Z r 4 v) φ c χ ∧
      (∀ᶠ r in trail,∀w:RG17.Free R.family 4,master L 4 r (deposit r w)=J r 4 w ∧
        ∀N per,L.level r ≤ N→quota R.family 4 (L.level r) N per (atRef L 4 r (N,per) (deposit r w)) ≤
          R.family.S.a (L.level r)^4*(β (L.level r)^e*‖w‖)) ∧
      ∀q:ℕ,∀ε>0,∀ᶠr in trail,
        let k:=berth R (2*1+q+1+25) (L.level r)
        ∀hr:0<r,∀ᶠz:ℕ×ℕ in U,∃live:k<z.1,
        let marks:=Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (atRef L 4 r z (a r)) (fun _=>atRef L 4 r z (b r))
        let inherited:=earlier R (per:=z.2) live.le marks (dilate hr φ)
        |χ c|/2 < σ*χ inherited ∧ ‖inherited-c‖ ≤ ε ∧ ‖inherited-cov r‖ ≤ ε*(g r)^q ∧
          |Value F L a b χ φ hr z-χ inherited| ≤ ε*(g r)^q

def Captured (δ g : ℝ → ℝ) : Prop :=
  ∃ (D:Profiles R 4) (j:D.probes.index) (v₀:(standard R.family.labels).Ref 4)
    (hs:D.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 v₀)
    (e:ℕ) (deposit:ℝ→RG17.Free R.family 4→R.family.label 4) (χ:ℂ→L[ℝ]ℝ) (σ:ℝ),
    Row (H:=H) (U:=U) F J Z L δ g D j v₀ hs e deposit χ σ

include lead paid simple funded subsidy pace hB level chosen E pegs in
theorem original {A:ℝ→Spin.change S 4} {δ g:ℝ→ℝ} (same:∀ᶠr in trail,J r 4=A r)
    (cent:∀ᶠr in trail,AlignV F.room.kernel F.sector H (A r)) (cal:TendC F A δ) (coupling:Coupling G g) :
    Captured (H:=H) (U:=U) F J Z L δ g := by
  obtain ⟨D,sites,K,_hK,decode⟩:=WilsonMatrixTicketLanesSmearedPair.fixed F J Z lead paid simple 4
  obtain ⟨j,v₀,hs,e,deposit,claim⟩:=WilsonInvariantActionSubmittedCapture.original F J Z lead paid
    simple funded subsidy pace L hB level chosen bank E pegs D sites K decode same cent cal coupling
  let φ:=WilsonInvariantActionCalibratedColumn.packet v₀ hs (test D j)
  let v:=(Bel R.family.book).project 4 v₀
  let a:=fun r=>deposit r (stepField R.family)
  let b:=fun r=>deposit r (freeInput F J Z 4 r v)
  let y:=fun r=>homogeneous F J Z r 4 v
  let cov:=fun r=>tested (J r 4 (stepField R.family)) (y r) r φ
  let c:=tree (D.probes.shell j) (test D j) H 4 (stepField R.family)
  obtain ⟨nonzero,limit,ward,market,old⟩:=claim
  have φreal:∀x,φ x=((φ x).re:ℂ):=packet_real v₀ hs (test D j) (fun _=>rfl)
  obtain ⟨χ,detected⟩:=WilsonMatrixOriginalSignedPanel.on_column F J simple same cal coupling y φ φreal c nonzero limit
  have booked:=WilsonMatrixOriginalFiledPanel.purchased F J L chosen simple same cal coupling a b y φ
    φreal c χ detected (pegs.level.growing.eventually_ge_atTop (R.family.ref 4)) (by
      filter_upwards [old 0 1 one_pos] with r price
      exact ⟨price.1,price.2.1⟩)
  let σ:=orientation (χ c)
  have sgn:σ=1 ∨ σ= -1:=orientation_cases _
  have orient:σ*χ c=|χ c|:=orientation_abs _
  have dpos:0< |χ c|:=booked.1
  refine ⟨D,j,v₀,hs,e,deposit,χ,σ,detected.1,sgn,orient,dpos,limit,ward,booked,market,?_⟩
  intro q ε he
  let η:=min (ε/2) (|χ c|/8)
  have ep:0<η:=lt_min (by linarith) (by linarith)
  have signedLimit:Tendsto (fun r=>σ*χ (cov r)) trail (𝓝 |χ c|):=by
    rw [←orient]
    exact tendsto_const_nhds.mul ((χ.continuous.tendsto _).comp limit)
  have gap:=signedLimit.eventually (lt_mem_nhds (show 3*|χ c|/4< |χ c| by linarith))
  have small:∀ᶠr in trail,g r≤1:=(coupling.conforms simple).eventually (ge_mem_nhds zero_lt_one)
  have leading:∀ᶠr in trail,‖cov r-c‖<ε/2:=by
    simpa only [dist_eq_norm] using Metric.tendsto_nhds.mp limit (ε/2) (half_pos he)
  filter_upwards [booked.2,old q η ep,gap,small,coupling.positive,leading] with r filed saved far low gp free
  intro k hr
  have near:∀ᶠz in U,dist (Value F L a b χ φ hr z) (χ (cov r)) < ε/2*(g r)^q :=
    Metric.tendsto_nhds.mp (filed hr).2.1 _ (by positivity)
  filter_upwards [near,saved.2.2 hr] with z actual earlier_paid
  obtain ⟨live,price⟩:=earlier_paid
  let marks:=Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (atRef L 4 r z (a r)) (fun _=>atRef L 4 r z (b r))
  let lower:=earlier R (per:=z.2) live.le marks (dilate hr φ)
  have ab:|χ lower-χ (cov r)|≤η*(g r)^q:=(component χ detected.1 _ _).trans price
  have fee:η*(g r)^q ≤ ε/2*(g r)^q:=mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg gp.le _)
  have relative:η*(g r)^q ≤ |χ c|/8:=
    (mul_le_of_le_one_right ep.le (pow_le_one₀ gp.le low)).trans (min_le_right _ _)
  have first:‖lower-c‖≤ε:=by
    have d:‖lower-c‖≤‖lower-cov r‖+‖cov r-c‖:=by simpa only [dist_eq_norm] using dist_triangle lower (cov r) c
    have cap:η*(g r)^q ≤ ε/2:=(mul_le_of_le_one_right ep.le (pow_le_one₀ gp.le low)).trans (min_le_left _ _)
    exact d.trans ((add_le_add (price.trans cap) free.le).trans_eq (add_halves ε))
  have total : η*(g r)^q ≤ ε*(g r)^q := fee.trans (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg gp.le _))
  refine ⟨live,sign_lower sgn far (ab.trans relative) dpos,first,price.trans total,?_⟩
  have tri:=abs_sub_le (Value F L a b χ φ hr z) (χ (cov r)) (χ lower)
  rw [abs_sub_comm (χ (cov r))] at tri
  rw [Real.dist_eq] at actual
  exact tri.trans ((add_le_add actual.le (ab.trans fee)).trans_eq (by ring))

end YM.Integration.WilsonMatrixOriginalEarlierPanel
