import YM.Integration.WilsonMatrixTicketLanesRegisteredProfile
import YM.Integration.WilsonMatrixTicketLanesConnectedIndependent

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
universe u
namespace YM.Integration.WilsonMatrixTicketLanesRegisteredWard
open Filter Function Set Finset MeasureTheory Lattice Wilson RG Tree Precision RG17 Source Marker Extraction Extraction.Order Spec
open Table Climb Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS OPE OPE.Therm Next.UVStress Next.Rank.Price
open PhysicalNext.Repeat.Legato SharpGram.Lenses FVA2 FVA2.Register Pert.Asymptotics
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMatrixTicketLanesSmearedRows
open WilsonInvariantActionPairProbe WilsonInvariantActionSpectatorPrices WilsonInvariantActionCalibratedColumn WilsonInvariantActionPairCovariance
open Trace.Sundial WilsonLimitConstruction WilsonMatrixOriginalEarlierPanel WilsonMatrixOriginalLogarithmicRate WilsonMatrixOriginalReportingMargin
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book} (F:Final R.family f S)
  (J:ℝ→tower S) (Z:WilsonPrescription G) {H:(Bel R.family.book).Hierarchy} (L:Layout F)
  {U:Filter (ℕ×ℕ)}

/-- The remaining signed response belongs to the actual unmasked primary and its
earlier signed field, with the registered pin, both parent sites and both means retained. -/
def Witness (g:ℝ→ℝ) (a b:ℝ→R.family.label 4) (φ:Test 2) (c:ℂ) (χ:ℂ→L[ℝ]ℝ) (σ:ℝ):Prop:=
  ∀q cap:ℕ,∀ ε>0,∀ᶠr in trail,∀hr:0<r,∀ᶠz:ℕ×ℕ in U,∃k,∃date:L.level r=k+1,∃future:L.level r<z.1,
    let marks:=Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (atRef L 4 r z (a r)) (fun _=>atRef L 4 r z (b r))
    let old:=WilsonInvariantActionCapturedProfile.earlier R (per:=z.2) future.le marks (dilate hr φ)
    let stable:=WilsonMatrixTicketLanesRegisteredProfile.unmaskedProfile R (per:=z.2) future.le marks (dilate hr φ)
    ‖old-stable‖ ≤ ε*(g r)^q ∧
    ∀u:Directions G (R.family.side k z.2),(∀i,‖u i‖ ≤ (cap:ℝ)+1)→
      let fresh:=WilsonMatrixTicketLanesConnectedSigned.tested R F L 4 4 a b hr φ date (p:=z.2) future.le u
      ‖stable-fresh-c‖ ≤ ε ∧ |χ c|/8<σ*χ (stable-fresh)

theorem on_row (simple:G.Simple) {ρ:ℝ} {T:Campaign R} (W:Campaign.Pillars R T)
    (funded:FundedOriginalProperties.{u} simple ρ W) (pace:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F J) (obey:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (chosen:U ≤ L.lens) {B:ℕ} (wide:17 ≤ B) (level:L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B)
    {δ g:ℝ→ℝ} (coupling:Coupling G g) (D:Profiles R 4) (j:D.probes.index) (v₀:(standard R.family.labels).Ref 4)
    (hs:D.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 v₀) (e:ℕ)
    (deposit:ℝ→RG17.Free R.family 4→R.family.label 4) (χ:ℂ→L[ℝ]ℝ) (σ:ℝ)
    (record:Row (H:=H) (U:=U) F J Z L δ g D j v₀ hs e deposit χ σ):
    let φ:=WilsonInvariantActionCalibratedColumn.packet v₀ hs (test D j)
    let v:=(Bel R.family.book).project 4 v₀
    let a:=fun r=>deposit r (stepField R.family)
    let b:=fun r=>deposit r (freeInput F J Z 4 r v)
    let c:=tree (D.probes.shell j) (test D j) H 4 (stepField R.family)
    WilsonMatrixTicketLanesConnectedMargin.Remaining (U:=U) R F L a b φ c χ σ→
      Witness (U:=U) R F L g a b φ c χ σ:=by
  let φ:=WilsonInvariantActionCalibratedColumn.packet v₀ hs (test D j)
  let v:=(Bel R.family.book).project 4 v₀
  let a:=fun r=>deposit r (stepField R.family)
  let b:=fun r=>deposit r (freeInput F J Z 4 r v)
  let c:=tree (D.probes.shell j) (test D j) H 4 (stepField R.family)
  dsimp only []
  intro earlier q cap ε ep
  have price:=WilsonMatrixTicketLanesRegisteredProfile.on_row R F J Z L simple W funded pace lead obey
    chosen wide level coupling D j v₀ hs e deposit χ σ record
  have cpos:0< |χ c|:=record.2.2.2.1
  let η:=min (ε/2) (|χ c|/8)
  have hp:0<η:=lt_min (half_pos ep) (div_pos cpos (by norm_num))
  have ηε:η ≤ ε/2:=min_le_left ..
  have ηc:η ≤ |χ c|/8:=min_le_right ..
  have projected(z:ℂ):|χ z| ≤ ‖z‖:=by rcases record.1 with rfl|rfl;exact Complex.abs_re_le_norm z;exact Complex.abs_im_le_norm z
  have signed(z:ℂ):-‖z‖ ≤ σ*χ z:=by
    have :=projected z;rcases record.2.1 with rfl|rfl <;> simp only [one_mul,neg_one_mul] <;>
      linarith only [(abs_le.mp this).1,(abs_le.mp this).2]
  filter_upwards [price q ε ep,price 0 η hp,earlier cap (ε/2) (half_pos ep)] with r all zero stays
  intro hr
  filter_upwards [all hr,zero hr,stays hr] with z allBill lowBill before
  obtain ⟨_,full⟩:=allBill
  obtain ⟨_,small⟩:=lowBill
  obtain ⟨k,date,future,panel⟩:=before
  refine ⟨k,date,future,full,?_⟩
  let w:=Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (atRef L 4 r z (a r)) (fun _=>atRef L 4 r z (b r))
  let old:=WilsonInvariantActionCapturedProfile.earlier R (per:=z.2) future.le w (dilate hr φ)
  let newrow:=WilsonMatrixTicketLanesRegisteredProfile.unmaskedProfile R (per:=z.2) future.le w (dilate hr φ)
  have fee:‖newrow-old‖ ≤ η:=by rw [norm_sub_rev];simpa only [pow_zero,mul_one] using small
  intro u held
  let fresh:=WilsonMatrixTicketLanesConnectedSigned.tested R F L 4 4 a b hr φ date (p:=z.2) future.le u
  obtain ⟨close,margin⟩:=panel u held
  change ‖old-fresh-c‖ ≤ ε/2 at close
  change |χ c|/4<σ*χ (old-fresh) at margin
  change ‖newrow-fresh-c‖ ≤ ε ∧ |χ c|/8<σ*χ (newrow-fresh)
  constructor
  · rw [show newrow-fresh-c=(newrow-old)+(old-fresh-c) by ring]
    exact (norm_add_le _ _).trans (by linarith only [fee,close,ηε])
  · rw [show newrow-fresh=(newrow-old)+(old-fresh) by ring,map_add,mul_add]
    linarith only [signed (newrow-old),fee,ηc,margin]


def Fields (B:ℕ) (δ g:ℝ→ℝ) : Prop :=
  ∃(D:Profiles R 4)(j:D.probes.index)(v₀:(standard R.family.labels).Ref 4)
    (hs:D.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 v₀)(e:ℕ)
    (deposit:ℝ→RG17.Free R.family 4→R.family.label 4)(χ:ℂ→L[ℝ]ℝ)(σ:ℝ),
    let φ:=WilsonInvariantActionCalibratedColumn.packet v₀ hs (test D j)
    let v:=(Bel R.family.book).project 4 v₀
    let a:=fun r=>deposit r (stepField R.family)
    let b:=fun r=>deposit r (freeInput F J Z 4 r v)
    let cov:=fun r=>tested (J r 4 (stepField R.family)) (homogeneous F J Z r 4 v) r φ
    let c:=tree (D.probes.shell j) (test D j) H 4 (stepField R.family)
    Row (H:=H) (U:=U) F J Z L δ g D j v₀ hs e deposit χ σ ∧ Rate (U:=U) F L B g a b φ cov ∧
    LeadingRow (U:=U) F L a b φ c χ σ ∧ WilsonMatrixOriginalCapturedInverse.Recovered (U:=U) F L g a b χ σ φ c ∧
    WilsonMatrixTicketLanesConnectedSigned.Negligible R F L U 4 4 g a b φ ∧
    WilsonMatrixTicketLanesConnectedMargin.Remaining (U:=U) R F L a b φ c χ σ ∧
    Witness (U:=U) R F L g a b φ c χ σ

theorem issued (simple:G.Simple) {ρ:ℝ} {T:Campaign R} (W:Campaign.Pillars R T)
    (funded:FundedOriginalProperties.{u} simple ρ W) (pace:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F J) (obey:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d) (chosen:U ≤ L.lens)
    {B:ℕ} (wide:17 ≤ B) (level:L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B)
    {δ g:ℝ→ℝ} (coupling:Coupling G g)
    (input:WilsonMatrixTicketLanesConnectedWitness.Fields (H:=H) (U:=U) R F J Z L B δ g):
    Fields (H:=H) (U:=U) R F J Z L B δ g:=by
  obtain ⟨D,j,v,site,e,deposit,χ,σ,record,rate,leading,inverse,fresh,older⟩:=input
  exact ⟨D,j,v,site,e,deposit,χ,σ,record,rate,leading,inverse,fresh,older,
    on_row R F J Z L simple W funded pace lead obey chosen wide level coupling D j v site e deposit χ σ record older⟩

def Measured (simple:G.Simple) (Q:MS.Land.Prescription (Press.portDeck G)) : Prop :=
  ∀(B:ℕ),17  ≤  B → ∀ v:Extraction.Order,
    ∃(w:Extraction.Order)(S:Table R.family.book)(F:Final R.family (v.refine w) S)
      (H:(Bel R.family.book).Hierarchy)(J:ℝ→tower S)(A:ℝ→Spin.change S 4)(δ:ℝ→ℝ)(L:Layout F),
      Leading F J ∧ (∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d) ∧ (∀ᶠr in trail,J r 4=A r) ∧
      TendC F A δ ∧ Coupling G (glo A) ∧ L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B ∧
      L.lens  ≤  (v.refine w).fuse ∧ WilsonGaussianProbeMatrix.Filed F J L Q ∧
      Fields (H:=H) (U:=L.lens) R F J Z L B δ (glo A) ∧
      WilsonMatrixTicketLanesConnectedIndependent.Printed (H:=H) R F J Z L δ (glo A)

theorem on_run (simple:G.Simple) {ρ:ℝ} {T:Campaign R} (W:Campaign.Pillars R T)
    (funded:FundedOriginalProperties.{u} simple ρ W) (pace:WilsonWindowReportingPace.Slow R.kit)
    (Q:MS.Land.Prescription (Press.portDeck G)) (bought:WilsonMatrixTicketLanesConnectedIndependent.Measured R Z simple Q):
    Measured R Z simple Q:=by
  intro B wide v
  obtain ⟨w,S,F,H,J,A,δ,L,lead,obey,grade,flow,coupling,level,within,booked,observed,independent⟩:=bought B wide v
  exact ⟨w,S,F,H,J,A,δ,L,lead,obey,grade,flow,coupling,level,within,booked,
    issued R F J Z L simple W funded pace lead obey le_rfl wide level coupling observed,independent⟩

end YM.Integration.WilsonMatrixTicketLanesRegisteredWard
