import YM.Integration.WilsonMatrixOriginalIndependentSettlement
import YM.Integration.WilsonMatrixOriginalIndependentPrices
import YM.Integration.WilsonMatrixOriginalParentPurchase

noncomputable section
namespace YM.Integration.WilsonMatrixOriginalIndependentCoupon
open FVA2 MS.Local.Physical MS.Menus
open Filter Function Set Finset MeasureTheory Lattice Wilson RG Tree Precision RG17 Source Marker Extraction Spec
open Table Climb Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS OPE OPE.Therm
open Next.UVStress Next.Rank.Price PhysicalNext.Repeat.Legato SharpGram.Lenses FVA2 FVA2.Register
open RGComparison.Core16 RGComparison.Core16.Spool FVA2.CityHistory Pert.Asymptotics
open WilsonMatrixTicketLanesReportedOneBlock WilsonMatrixTicketLanesRegulatorCoupon
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMatrixTicketLanesSmearedRows
open WilsonInvariantActionPairProbe WilsonInvariantActionCalibratedColumn WilsonMatrixOriginalEarlierPanel
open private volume_bill from YM.Integration.WilsonInvariantActionPromotedPair
open private coupling_bound from YM.Integration.WilsonInvariantActionPromotedRegular
open scoped Classical BigOperators Topology

open WilsonMatrixOriginalIndependentForest WilsonMatrixOriginalIndependentLimit
open WilsonMatrixOriginalIndependentSettlement WilsonMatrixOriginalIndependentPrices
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book} (F:Final R.family f S)
    (L:Layout F) {U:Filter (ℕ×ℕ)}

def Filed (B:Deck G) (τ:ℕ→ℝ) (e:ℕ) (g:ℝ→ℝ) (a b:ℝ→R.family.label 4) (φ:Test 2) : Prop :=
  ∀ (n:ℕ) (pick:Fin n→Fin 2) (q cap:ℕ) (ε:ℝ),0<ε→∀ᶠr in trail,let m:=L.level r
  ∀hr:0<r,∀ᶠz:ℕ×ℕ in U,∃(old:ℕ)(stepDate:m=old+1)(live:m<z.1),∃ large:Bid.Larger (G:=G) (step R z.2 stepDate),
  ∀(T:Forest (step R z.2 stepDate).ratio) (u:Pins G (R.family.side old z.2))
    (tag:(step R z.2 stepDate).Choices) (v:(Descent.nil (top:=R.family.side m z.2)).Tags),
    (∀j,‖u j‖≤(cap:ℝ)+1) →
    let top:=fun i:Fin n=>atRef L 4 r z ((Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (a r) (fun _=>b r)) (pick i))
    let d:=fun _:Fin n=>4
    let order:=q+1+2*((∑_i:Fin n,e)+1)
    let seat:=fun (x:Fin 2→Site (R.family.side z.1 z.2)) (i:Fin n)=>(R.family.S.toDepth live.le z.2).parent (x (pick i))
    let c:=fun x=>WilsonExternalMeshMass.charge R.family (dilate hr φ) x
    ‖(∑x,c x*fresh R d z.1 z.2 top stepDate u (seat x))-
      (∑x,c x*book R B (fun i=>fixed R B F L τ r ((Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (a r) (fun _=>b r)) (pick i)))
        (WilsonMatrixTicketLanesRetainedFare.reading R (N:=z.1) d order stepDate large T u (seat x) tag v))‖≤ε*(g r)^q

private theorem weighted {X I:Type} [Fintype X] [Fintype I] (B:Deck G) (c:X→ℂ)
    (a b:I→Glyph B 4→ℂ) (v:X→(I→Index R)→ℂ) {C:ℝ} (price:∀x j,‖v x j‖≤C) :
    ‖(∑x,c x*book R B a (v x))-(∑x,c x*book R B b (v x))‖≤
      (∑x,‖c x‖)*(WilsonMatrixOriginalIndependentSettlement.change R B a b*C) := by
  rw [←sum_sub_distrib,Finset.sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum ?_)
  intro x _
  rw [←mul_sub,norm_mul]
  exact mul_le_mul_of_nonneg_left (settle R B a b (v x) (price x)) (norm_nonneg _)

/-- The identical earlier reporter spends fixed arm weights against its independently
generated finite forecast. Its error is uniform over the full compact common pin field and all forest data. -/
theorem cleared (B:Deck G) (simple:G.Simple) (paid:WilsonMatrixTicketLanesReportedPrepaid.Paid G R.kit)
    (U:Ultrafilter (ℕ×ℕ)) (cut:(U:Filter (ℕ×ℕ))≤L.lens) (grow:Tendsto L.level trail atTop)
    (τ:ℕ→ℝ) (lim:∀r w,R.family.ref 4≤L.level r→
      Tendsto (fun z:ℕ×ℕ=>coefficient R B (L.level r) z.1 z.2 (atRef L 4 r z w))
        (U:Filter (ℕ×ℕ)) (𝓝 (fixed R B F L τ r w)))
    (e:ℕ) (g:ℝ→ℝ) (positive:∀ᶠr in trail,0<g r)
    (a b:ℝ→R.family.label 4) (φ:Test 2)
    (signed:WilsonMatrixOriginalMatchedForest.Signed (U:=L.lens) F L e g a b φ) :
    Filed F L (U:=(U:Filter (ℕ×ℕ))) B τ e g a b φ := by
  intro n pick q cap ε ep
  let d:=fun _:Fin n=>4
  let h:=q+1+2*((∑_i:Fin n,e)+1)
  let M:=(∫x,‖φ x‖)+1
  have prev:Tendsto (fun r=>L.level r-1) trail atTop:=tendsto_atTop.2 fun k=>
    (grow.eventually_ge_atTop (k+1)).mono fun r hr=>by change k≤L.level r-1;omega
  have prices:=prev.eventually (WilsonMatrixOriginalIndependentPrices.reading R simple paid d h cap)
  filter_upwards [signed n pick q cap (ε/2) (half_pos ep),prices,grow.eventually_ge_atTop (R.family.ref 4),positive]
    with r entered billed age gp
  intro m hr
  let w:=fun i:Fin n=>(Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (a r) (fun _=>b r)) (pick i)
  let vary:=fun (z:ℕ×ℕ)(i:Fin n)=>coefficient R B m z.1 z.2 (atRef L 4 r z (w i))
  let ready:=fun i=>fixed R B F L τ r (w i)
  let C:=max 0 (bound R (m-1) h)
  let E:=fun z=>WilsonMatrixOriginalIndependentSettlement.change R B (vary z) ready
  have settled:Tendsto (fun z=>M*(E z*C)) (U:Filter (ℕ×ℕ)) (𝓝 0) := by
    have v:=clear R B vary ready (fun i=>lim r (w i) age)
    simpa only [E,zero_mul,mul_zero] using (v.mul_const C).const_mul M
  let ψ:=dilate hr φ
  have total:=(WilsonExternalMeshMass.funded R.family f ψ ψ.continuous ψ.hasCompactSupport
    (show (0:ℝ)<1 by norm_num)).filter_mono (cut.trans L.certified)
  have slack:0<(ε/2)*(g r)^q:=mul_pos (half_pos ep) (pow_pos gp q)
  filter_upwards [(entered hr).filter_mono cut,total,settled.eventually (gt_mem_nhds slack)] with z invoice budget residue
  obtain ⟨old,date,live,large,spent⟩:=invoice
  refine ⟨old,date,live,large,?_⟩
  intro T u tag v inside
  let top:=fun i=>atRef L 4 r z (w i)
  let seat:=fun (x:Fin 2→Site (R.family.side z.1 z.2)) (i:Fin n)=>(R.family.S.toDepth live.le z.2).parent (x (pick i))
  let c:=fun x=>WilsonExternalMeshMass.charge R.family (N:=z.1) (p:=z.2) ψ x
  let values x:=WilsonMatrixTicketLanesRetainedFare.reading R (N:=z.1) d h date large T u (seat x) tag v
  have old_eq:m-1=old:=by omega
  subst old
  have prices':∀x j,‖values x j‖≤C := by
    intro x j
    exact (billed date z.1 z.2 live.le large T u (seat x) tag v inside j).trans (le_max_right _ _)
  let actual x:=fresh R d z.1 z.2 top date u (seat x)
  have first:‖(∑x,c x*actual x)-(∑x,c x*book R B (vary z) (values x))‖≤(ε/2)*(g r)^q := by
    have hfirst:=spent T u tag v inside
    simpa only [WilsonMatrixOriginalIndependentForest.forecast_eq R B simple,
      independent,book,c,values,vary,top,actual,d,h,w,seat,ψ] using hfirst
  have amount:∑x,‖c x‖≤M:=by simpa only [c,M,ψ,volume_bill] using budget
  have nonnegative:0≤E z*C := mul_nonneg
    (Finset.sum_nonneg fun _ _=>mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun _ _=>norm_nonneg _)) (le_max_left _ _)
  have second:‖(∑x,c x*book R B (vary z) (values x))-(∑x,c x*book R B ready (values x))‖≤(ε/2)*(g r)^q :=
    (weighted B c (vary z) ready values prices').trans ((mul_le_mul_of_nonneg_right amount nonnegative).trans residue.le)
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add first second).trans (by ring_nf;exact le_rfl))

end YM.Integration.WilsonMatrixOriginalIndependentCoupon
