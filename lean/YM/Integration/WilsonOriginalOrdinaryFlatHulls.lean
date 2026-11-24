import YM.Integration.WilsonOriginalFlatHull
import YM.Integration.WilsonFiniteOrdinaryTail
import YM.Integration.WilsonReceivedOrdinaryFaces

/-! Compare a complete ordinary face on the original older flat. Each connected
block stays at its own paid front. The original posterior sums the failed
halos once, after the disconnected ordinary products have been reconstructed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOrdinaryFlatHulls
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner OPE.Therm
open scoped BigOperators Classical


open Comparison.Density Comparison.Density.Transport Comparison.Density.Mirrors
open AnalyticBridge.SectorAffine.Offset

open Multi
open scoped BigOperators

variable {V:Type} [DecidableEq V] [Fintype V] {J:Census V}

def cost (s:J.Mode)(M:ℝ) : ℝ := ((shards J s).card:ℝ)*(1+M)^s.val.card

private theorem sumBound (s:J.Mode)(f h:Poly J)(quiet:f.part J.quiet=0 ∧ h.part J.quiet=0)
    {C:ℝ}(bound:∀q∈shards J s,‖(∏t∈q.val,f.part t.val)-∏t∈q.val,h.part t.val‖≤C):
    ‖(Poly.pass f).part s-(Poly.pass h).part s‖≤((shards J s).card:ℝ)*C:=by
  rw [YM.RG02.Marks.pass_partition quiet.1,YM.RG02.Marks.pass_partition quiet.2,←sum_sub_distrib]
  exact (norm_sum_le ..).trans ((sum_le_sum bound).trans_eq (by simp))

def change (s:J.Mode)(M δ:ℝ):ℝ :=
  ∑ q∈shards J s,(q.val.card:ℝ)*δ*(1+M+δ)^q.val.card

/-- The marked unit, and every proper product, belong to the same ordinary read. -/
theorem ordinary (s:J.Mode)(f h:Poly J)(quiet:f.part J.quiet=0 ∧ h.part J.quiet=0)
    {M δ:ℝ}(mp:0≤M)(dp:0≤δ)
    (bills:∀t:Hot J,t.val.val⊆s.val → ‖h.part t.val‖≤M ∧ ‖f.part t.val-h.part t.val‖≤δ):
    ‖(Poly.pass f).part s-(Poly.pass h).part s‖≤change s M δ:=by
  have price:=WilsonReceivedOrdinaryFaces.ordinary_on f h (fun _=>1) (fun _=>zero_lt_one)
    quiet.1 quiet.2 δ (1+M) dp (by linarith only [mp,dp]) s
    (fun t ht=>by simpa [Poly.toll] using (bills t ht).2)
    (fun t ht=>by simpa [Poly.toll] using (bills t ht).1.trans (show M≤1+M by linarith))
  simpa [change,Poly.toll] using price

private theorem gross (s:J.Mode)(f h:Poly J)(quiet:f.part J.quiet=0 ∧ h.part J.quiet=0)
    {M:ℝ}(mp:0≤M)(bills:∀t:Hot J,t.val.val⊆s.val → ‖f.part t.val‖≤M ∧ ‖h.part t.val‖≤M):
    ‖(Poly.pass f).part s-(Poly.pass h).part s‖≤2*cost s M:=by
  unfold cost
  rw [show (2:ℝ)*((shards J s).card*(1+M)^s.val.card)=
    (shards J s).card*(2*(1+M)^s.val.card) by ring]
  apply sumBound s f h quiet
  intro q hq
  have each (a:Poly J)(bound:∀t:Hot J,t.val.val⊆s.val → ‖a.part t.val‖≤M):
      ‖∏t∈q.val,a.part t.val‖≤(1+M)^s.val.card:=by
    rw [norm_prod]
    calc
      _≤∏_t∈q.val,(1+M) := prod_le_prod (fun _ _=>norm_nonneg _)
        (fun t ht=>(bound t (WilsonReceivedOrdinaryFaces.contained s q hq t ht)).trans (by linarith))
      _=(1+M)^q.val.card := by simp
      _≤_ := pow_le_pow_right₀ (by linarith only [mp]) (WilsonFiniteOrdinaryTail.blocks s q hq)
  have A:=each f (fun t ht=>(bills t ht).1)
  have B:=each h (fun t ht=>(bills t ht).2)
  exact (norm_sub_le ..).trans ((add_le_add A B).trans_eq (by ring))

/-- A paid angular crop of two particular connected words, with its original root. -/
structure Row {G:Gauge}{n:Side}(B:BudgetPoint)(L:LinkTube G)(o:Site n)(f h:Config G n→ℂ) where
  tail : Config G n→ℂ
  retained : ℕ
  depth : ℕ
  width : ℝ
  jet : ℝ
  high : ℝ
  tailJet : ℝ
  tailValue : ℝ
  crop : WilsonOriginalFlatHull.Crop B L o f h tail retained depth width jet high tailJet tailValue

def Row.price {G:Gauge}{n:Side}{B:BudgetPoint}{L:LinkTube G}{o:Site n}{f h:Config G n→ℂ}
    (r:Row B L o f h):ℝ :=
  groupPrice L 0*((r.retained:ℝ)*(r.jet+r.tailJet)+r.high*r.width^r.retained)+r.tailValue

variable {G:Gauge}(R:Run G){N per m k b:ℕ}(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)
   (Ψ:∀j,RG.Rep G (R.family.side j per))(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
   (cut:b<N){d:ℕ}{F:Frame G d}(S:SectionData F)(A:Hol G)
   (simple:G.Simple)(way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
   (Q:D.Tab R.rolls)(ticket:TicketP R.alloy R.kit D Q){u:ℕ}(floor:m ≤ u)(ub:u ≤ b)
   (fixed:WilsonSingleHardRadius.first R simple ≤ u)
local notation "κ" => LocalComparison.forcedDivisor R.family b
local notation "β" => R.alloy.B.a.clock.hatBeta b
local notation "Space" => Config G (R.family.side b per)




include course cut way ticket floor ub fixed S A in
theorem original (capture:WilsonCenteredCaptureClock.first R simple ≤ b)(p d₀:ℕ){tol:ℝ}(positive:0<tol)
    (s:J.Mode)(late:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple
      (p+d₀*s.val.card) positive)).choose ≤ b)
    {α:ℝ}(strength:(Ψ b).p.supportExponent≤α)(L:LinkTube G)(o:V→Site (R.family.side b per))
    (front:Hot J→V)(member:∀t,front t∈t.val.val)
    (F I:Space→Poly J)(quiet:∀U,(F U).part J.quiet=0 ∧ (I U).part J.quiet=0)
    (borel:Measurable (fun U=>(Poly.pass (F U)).part s-(Poly.pass (I U)).part s))
    {M δ:ℝ}(mp:0≤M)(dp:0≤δ)
    (salary:∀U (t:Hot J),t.val.val⊆s.val → ‖(F U).part t.val‖≤M*β^d₀ ∧ ‖(I U).part t.val‖≤M*β^d₀)
    (words:∀(t:Hot J),t.val.val⊆s.val → Row (Ψ b).p L (o (front t))
      (fun U=>(F U).part t.val) (fun U=>(I U).part t.val))
    (due:∀t ht,(words t ht).price≤δ)
    {i:ℕ}(ui:u ≤ i)(ib:i+1 ≤ b):
    ‖actualTransport R.family (N:=N) (fun U=>(Poly.pass (F U)).part s-(Poly.pass (I U)).part s)
      ((Nat.le_succ i).trans ib) 1‖≤change s (M*β^d₀) δ+
        (2*cost s M)*(s.val.card:ℝ)*(4*Real.exp (α+2))*tol/β^p:=by
  have inc:1≤β :=(R.alloy.B.a.fits.delayed b).le
  have growth:1≤β^d₀:=one_le_pow₀ inc
  have money:0≤M*β^d₀:=mul_nonneg mp (zero_le_one.trans growth)
  have cp:0≤change s (M*β^d₀) δ:=by unfold change;apply sum_nonneg;intro q _;positivity
  have cp':0≤cost s M:=by unfold cost;positivity
  apply WilsonOriginalFlatHaloRate.original R π Γ Ψ course cut S A simple way D Q ticket floor ub fixed
    capture p (d₀*s.val.card) positive late s.val o strength _ borel cp (by positivity) _ _ ui ib
  · intro U
    apply (gross s (F U) (I U) (quiet U) money (salary U)).trans
    have base:1+M*β^d₀≤(1+M)*β^d₀:=by rw [add_mul,one_mul];gcongr
    have priced:=pow_le_pow_left₀ (by linarith only [money]) base s.val.card
    unfold cost
    rw [mul_pow,←pow_mul] at priced
    calc
      _≤2*((shards J s).card*((1+M)^s.val.card*β^(d₀*s.val.card))) := by gcongr
      _=_:=by ring
  · intro U healthy
    apply ordinary s (F U) (I U) (quiet U) money dp
    intro t sub
    exact ⟨(salary U t sub).2,
      (WilsonOriginalFlatHull.healthy (words t sub).crop U (healthy (front t) (sub (member t)))).trans
        (due t sub)⟩

end YM.Integration.WilsonOriginalOrdinaryFlatHulls
end
