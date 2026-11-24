import YM.Integration.WilsonPositionProgramBlockedTrialInverse
/-! On the very same original funded hierarchy, the purchased before-length
readout covers each column of the nonbare trial cone. This gives an arbitrary
subpower over the entire trial interval, before either physical regulator. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonPositionProgramBlockedTrialSalary
open Function Filter Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open Push.PriceCompiler
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (shop:RG05Preconstruction.ReadoutPurchase R.b)
local notation "C₀" => R.family
local notation "H₀" => (C₀).path
local notation "J₀" => R.alloy.B.a.clock.J
local notation "F₀" => (C₀).labels.level
local notation "B₀" => (C₀).localSection
local notation "P₀" => (C₀).params

include shop
theorem column (i:ℕ):stock C₀ (i+1) ≤ RG05Readout.Copper.ld (H₀).levels i:=by
  let j:=J₀ (i+1)
  have quote:=shop.crossed j j 0 (le_refl _) (Nat.zero_le _)
  have pay:=(RG05Readout.Copper.cash_fill G 0 j R.metals.p.profile R.y).choose_spec
  let v:=RG05Readout.Copper.ash G 0 j R.metals.p.profile R.y
  have bound:(R.metals.p.profile j).columns≤v:=pay.2.1
  have pos:0≤v:=zero_le_one.trans pay.1
  have enough:=bound.trans ((le_add_of_nonneg_right pos).trans quote.supp)
  change (R.alloy.B.a.params (i+1)).columns ≤ RG05Readout.Copper.lamp (R.alloy.B.a.S.block i) j
  simpa only [params_eq R.alloy.B.valid (i+1),block_eq R.alloy.B.valid i] using enough

theorem interval (b n:ℕ):WilsonPositionProgramBlockedTrialCone.cost R b n ≤ stringCost C₀ (Nat.le_add_right b n):=by
  induction n with
  | zero=>exact (string_base (C:=C₀) (m:=b)).ge
  | succ n ih=>
    rw [string_next (Nat.le_add_right b n)]
    exact mul_le_mul (column R shop _) ih (WilsonPositionProgramBlockedTrialCone.cost_nonneg R b n)
      (zero_le_one.trans (lamp_nn (C:=C₀) _))

theorem original (d:ℕ) (simple:G.Simple) {η:ℝ} (ep:0<η):
    ∀ᶠ b:ℕ in atTop,∀ (N p n:ℕ),∀ live:b+n≤N,
      let rep:=(H₀).rep N p b
      let out:=WilsonPositionProgramOriginalBlockedTrial.carried R d (p:=p) live 0
      ∃ A:(C₀).label d ≃ₗ[ℂ] (C₀).label d,∀ e:(C₀).label d,let w:=A.symm e
        (F₀ d).coeffSize w ≤ (2*Real.exp (η*((C₀).S.scale (b+n)-(C₀).S.scale b)))*(F₀ d).coeffSize e ∧
        ∃ q:Coefficient (F₀ d) ((C₀).side b p),q.Format 0 P₀ rep ∧
          q.remBound 0 rep (safety C₀ b) (2*stock C₀ b*(F₀ d).coeffSize e) ∧
          (F₀ d).coeffSize q.x≤2*(F₀ d).coeffSize e ∧ q.density 0 (B₀ d) rep=out w ∧
          projection (F₀ d) P₀ rep.p.threshold 0 q=e:=by
  obtain ⟨t,arrive⟩:=WilsonPositionProgramBlockedTrialInverse.original R d simple
  filter_upwards [eventually_ge_atTop t,string_paid (C:=C₀) ep] with b hb invoice
  intro N p n live
  obtain ⟨A,_,fit⟩:=arrive b hb N p n live
  refine ⟨A,fun e=>⟨(fit e).1.trans ?_,(fit e).2⟩⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    ((interval R shop b n).trans (invoice (b+n) (Nat.le_add_right b n))) zero_le_two)
    (Work.G08.size_nonneg _ e)

end YM.Integration.WilsonPositionProgramBlockedTrialSalary
end
