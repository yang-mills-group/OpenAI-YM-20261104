import YM.Integration.FVA1Physical.Wilson.InheritedFieldRows
import YM.Integration.FVA1Physical.Wilson.EmittedDegree
import YM.Integration.FVA1Physical.Wilson.CoarseFieldSchedule

/-! Two genuine consecutive RG blocks for an arbitrary fixed mixed physical
field. The output of the first normalized Wilson step is recalibrated by the
same physical scene's coupling and inserted in the next full distributed
Wilson step. A single selected Run pays every fixed order before the volume. -/
set_option autoImplicit false
set_option maxHeartbeats 1300000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MvPolynomial Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Bout MSbar.Duel MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Rolling MSbar.CrossH MSbar.Measuring
open PhysicalNext.Repeat.Legato Push.Uniform MSbar.Midpoint MSbar.Bakery.Film
open Extra.Iteration Push.PriceCompiler PhysicalNext.Repeat.Roost Next.Foundations
open RGComparison.Core16.Spool RGComparison.Core16.Lumen YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical Topology BigOperators
variable {G:Gauge} {μ:Type} [Fintype μ] {κ:μ→Type} [∀ a,Fintype (κ a)]

private def nextGate (J:Voice G) (clear:Clear G J) (simple:G.Simple) (H H':RG.Stage) (P:Patch)
    (K:KernelChoices) (p s h ℓ:ℕ) : ℝ :=
  if br:P.Branches K G then (eventually_atTop.mp (inherited_field_rows J clear (Next.Foundations.chart G)
    (chart_ok G) simple H H' P K br p (emittedDegree p) h s (by unfold emittedDegree; omega)
    (margin_pos ℓ))).choose else 0

private def nextMenu (J:Voice G) (clear:Clear G J) (simple:G.Simple) (H H':RG.Stage)
    (P:Patch) (K:KernelChoices) : ℝ :=
  ∑ e:Fin (H.order+1) × Fin (H.order+1) × Fin (H.order+1) × Fin (H.order+1),
    |nextGate J clear simple H H' P K e.1.val e.2.1.val e.2.2.1.val e.2.2.2.val|

private theorem nextGate_le (J:Voice G) (clear:Clear G J) (simple:G.Simple) (H H':RG.Stage)
    (P:Patch) (K:KernelChoices) {p s h ℓ:ℕ} (hp:p ≤ H.order) (hs:s ≤ H.order)
    (hh:h ≤ H.order) (hl:ℓ ≤ H.order) :
    nextGate J clear simple H H' P K p s h ℓ ≤ nextMenu J clear simple H H' P K := by
  let e:Fin (H.order+1) × Fin (H.order+1) × Fin (H.order+1) × Fin (H.order+1):=
    (⟨p,by omega⟩,⟨s,by omega⟩,⟨h,by omega⟩,⟨ℓ,by omega⟩)
  let f (x:Fin (H.order+1) × Fin (H.order+1) × Fin (H.order+1) × Fin (H.order+1)):=
    nextGate J clear simple H H' P K x.1.val x.2.1.val x.2.2.1.val x.2.2.2.val
  exact (le_abs_self (f e)).trans (single_le_sum (fun x _=>abs_nonneg (f x)) (mem_univ e))

theorem two_physical_field_blocks (I:∀ a,κ a→Lamp G) {goal:Qlocal.Schedule.Goal G}
    (extra:Qlocal.Schedule.Obtainable goal) (simple:G.Simple) (b₀:ℝ) (hb:0<b₀) :
    ∃ (R:PhysicalNext.Repeat.Legato.Run G) (u:G.ColorIndex),
      R.family.path.levels.clock.kernel.penalty=b₀ ∧ goal R.metals R.rolls R.alloy R.kit ∧
      R.metals.O=chart G ∧ ∀ (p s h L:ℕ), 6 ≤ s → ∀ (η:ℝ), 0<η →
      ∀ᶠ k:ℕ in atTop, ∀ N n,k ≤ N → ∃ S:Scene R.family.path.levels n (p+1+p),
        Realized R.alloy.B.kin N n k (p+1+p) (Lis.sun G u) S ∧
        ∀ j,k ≤ j → j+1<N → ∀ (F₁:Forest (R.family.path.levels.clock.op (j+1) n).ratio)
          (v₁:(R.family.path.levels.clock.op (j+1) n).Choices) (F:Forest (R.family.path.levels.clock.op j n).ratio)
          (v:(R.family.path.levels.clock.op j n).Choices),
          let E:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S F₁ v₁
          let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S F v
          let θ:=R.family.path.levels.clock.hatBeta
          ∀ (a:μ) (part:Bool) (b:Site A.f) (o:κ a→Site E.f),
            (∀ t:Slice (I a),separation (E.S.ratio.embed b) (legs (I a) o t).1 ≤ L*closeN (θ (j+2))) →
            let first:=emittedRows E R.metals.O (jointFieldBank (I a) E o part) p
            let input:=inheritedBank A (emittedDegree p) (S.action (j+1)) first
            ∀ i ≤ p,Vault (address A.F G) {b} (αm (θ (j+1))) s h 0
              (PowerSeries.coeff i (normalizedRows A R.metals.O input p)) (θ (j+1)^η) := by
  haveI:=simple.nontrivial_color
  have dim:0<G.lieDim:=by rw [Gauge.lieDim,←G.colorIso.finrank_eq];exact Module.finrank_pos
  let u₀:G.ColorIndex:=⟨0,dim⟩
  obtain ⟨J,clear⟩:=MSbar.Heath.vocals G
  let offer:=(extra.also (Qlocal.Schedule.vacuumInvoice_obtainable simple u₀ J clear)).also
    (Qlocal.Schedule.selectedThreshold_obtainable (G:=G) (nextMenu J clear simple))
  obtain ⟨R,u,kern,⟨⟨done,invo⟩,cut⟩,hc,first⟩:=all_orders_coarse_fields I offer simple b₀ hb
  have growth:Tendsto (fun j=>(R.alloy.B.a.params j).order) atTop atTop:=by
    apply tendsto_atTop.2;intro i
    filter_upwards [eventually_ge_atTop (R.t i)] with j hj
    exact (Nat.le_succ i).trans (((R.makes.stages i).2 j hj).1)
  have estate:=invo.1 growth
  have ch:=(R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books).1
  have merit:=townsR R.b R.Q R.T R.t R.stories R.doors ch
  refine ⟨R,u,kern,done,hc,?_⟩
  intro p s h L hs η hη
  obtain ⟨ℓ,hℓ⟩:=margin_eventually hη
  let ε:=margin ℓ
  let d:=p+1+p
  let m:=emittedDegree p
  let q:=h+2*Whisk.ribbon m d+1
  let δ:=inputSlack p m h (margin_pos ℓ)/2/2
  have hδ:0<δ:=half_pos (half_pos (inputSlack_pos p m h (margin_pos ℓ)))
  let nice:=max (max p s) (max h ℓ)
  filter_upwards [first p s q L hs 0 δ le_rfl hδ,Alto.skyline R.alloy.B d simple estate.levy merit s u hs,
    eventually_ge_atTop (R.t nice)] with k zone funds delay
  intro N n kN
  obtain ⟨S,realized,old⟩:=zone N n kN
  refine ⟨S,realized,?_⟩
  intro j kj jN F₁ v₁ F v E A θ a part b o near T input i hi
  have jN':j<N:=by omega
  have kj':k ≤ j+1:=by omega
  let H:=R.family.path.levels.params j
  let H':=R.family.path.levels.params (j+1)
  have high:nice ≤ H.order:=(Nat.le_succ nice).trans (((R.makes.stages nice).2 j (delay.trans kj)).1)
  dsimp only [nice] at high
  have branch:A.S.patch.Branches A.S.kernel G:=(R.family.path.levels.blocks j n).branches
  have eligible:nextGate J clear simple H H' A.S.patch A.S.kernel p s h ℓ ≤ θ j:=
    (nextGate_le J clear simple H H' _ _ (by omega) (by omega) (by omega) (by omega)).trans (cut j n)
  rw [nextGate,dif_pos branch] at eligible
  have prop:=(eventually_atTop.mp (inherited_field_rows J clear (chart G) (chart_ok G) simple H H'
    A.S.patch A.S.kernel branch p m h s (by unfold m emittedDegree; omega) (margin_pos ℓ))).choose_spec _ eligible
  have stage:=auditorium R.b R.Q R.T R.t R.stories R.doors ch J N n j jN' simple estate.sees
    (fun t=>invo.2.1 _ _ (R.alloy.B.valid.pays t) _ (step_paid R.alloy.B.a t))
  have usable:=prop A b rfl rfl stage
  dsimp only at usable
  have scale:tip G A.S.patch.L (θ j)=θ (j+1):=(Extra.Iteration.block_beta (a:=R.family.path.levels) j).symm
  rw [scale,←hc] at usable
  have trend:=(realized.budget (j+1) (by omega) kj').1
  have dots:=(funds N n S realized).1 (j+1) kj' (by omega)
  have w:Alto.Wedge A.T Alto.Dean (hatW (θ (j+1))) (Alto.cWidth (θ (j+1))) s p:=
    ⟨fun t ht=>dots.shares t (by dsimp only [d];omega)⟩
  obtain ⟨_,_,unit,_,_⟩:=realized.step (j+1) jN kj'
  have reset:= (funds N n S realized).2 (j+1) kj' jN
  apply Quote.widen (usable trend.bond ⟨fun t ht=>trend.plane.profile t (by omega)⟩ w T (S.action (j+1))
    unit (fun t ht=>reset t (by omega)) ?_ i hi) (Real.rpow_le_rpow_of_exponent_le (R.family.path.levels.fits.delayed (j+1)).le hℓ) le_rfl
  intro t ht
  have e:=(old (j+1) kj' jN F₁ v₁ a part b 0 (by simp) o near t ht).2
  have in₁:=(realized.budget (j+2) jN (by omega)).1
  refine ⟨?_,emitted_field_degree E R.metals.O (I a) o part p in₁.bond in₁.plane ht⟩
  simp only [smul_zero] at e
  dsimp only [T, E, A, θ, q, d, m, δ, sceneIssue] at e ⊢
  convert e using 1 <;> rfl

end YM.Integration.FVA1Physical.Wilson
