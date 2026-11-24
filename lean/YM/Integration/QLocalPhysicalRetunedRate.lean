import YM.Integration.QLocalPhysicalRetunedMeasurement
import YM.Integration.FullQLocalCostSubpower

/-! Relative smallness of the entire measured marked density after lowering
the forecast on the same actual Run. Each independent test and every original
coarse configuration, including the thermal set, follows the common tail. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalPhysicalRetunedRate

open Filter Lattice Wilson RG Marker Precision LocalComparison
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric FullQLocal.PreRun.CostProfile
open Comparison.RG02 QLocalVacuumOrderRestriction
open AnalyticBridge.VerifiedReset.Averaging WilsonLimitConstruction Pert.Asymptotics
open ActualRunInterpolatedPackets QLocalMarkedCouplingDifference
open scoped Classical Topology

theorem absorb {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {J:Request V}
    (R:Run G) (hG:G.Simple) (A:NumericSchedule R.family J) (K:NumericPrices A)
    (C:ℝ) (s p:ℕ) {η ε:ℝ} (hη:0<η) (hε:0<ε) :
    ∀ᶠ m:ℕ in atTop,∀ N period:ℕ,m<N →
      let g:=regulatorRun R.family N period (m+1)
      C*K.geometry m*A.admittedCost m^s*g^(p+1)≤ε*g^((p:ℝ)+1-η) := by
  have hg:ActualRunSubpowerShift.Subpower R K.geometry:=by
    intro e he
    obtain ⟨i,hi⟩:=K.subpower e he
    filter_upwards [eventually_ge_atTop i] with m hm N t hn using hi m hm N t hn
  have h₀:=scalar_subpower_constant R hG A (C/ε)
  have h₁:=scalar_subpower_mul R _ _ K.geometry_nonnegative h₀ hg
  have h₂:=scalar_subpower_pow R hG A _ A.admitted_cost_nonnegative
    (scalar_subpower_of_schedule R A) s
  have full:=scalar_subpower_mul R _ _ (fun m=>pow_nonneg (A.admitted_cost_nonnegative m) s) h₁ h₂
  filter_upwards [full η hη] with m hm N per hn
  let g:=regulatorRun R.family N per (m+1)
  have gp:0<g:=Currency.g_pos R.makes _ _ _ (Nat.succ_le_of_lt hn)
  calc
    _=ε*((C/ε*K.geometry m*A.admittedCost m^s)*g^(p+1)):=by
      field_simp [hε.ne']
      ring
    _≤ε*(g^(-η)*g^(p+1)):=mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hm N per hn) (pow_nonneg gp.le _)) hε.le
    _=_:=by rw [←Real.rpow_natCast,←Real.rpow_add gp]; congr 2; push_cast; ring

variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V} {J:Request V}
    (R:Run G) (hG:G.Simple) (A:NumericSchedule R.family J) (K:NumericPrices A)
include hG

variable (hT:ActualRunNativeComponentRecipe.Attached R)
    (readout:RG05Preconstruction.ReadoutPurchase R.b) (caps:Handoff.OutputCapacities)

include hT readout

/-- The scalar used for normalization is arbitrary. In particular it may be
the inverse of the actual positive coarse Wilson density at each single field.
The original selected, fully signed output is the exact reference measure. -/
theorem physical {p:ℕ} (hp:2≤p) (hq:p≤J.order) (r:ℕ) {ε:ℝ} (hε:0<ε) :
    ∀ᶠ m:ℕ in atTop,∀ (z:LocalFormal.Datum R.family Γ),z.level=m →
      ∀ (Y:Bulk.Chain R.family.path) (F:AnalyticInput J A z) (η:ℝ) (I:FullPreparedInputAt F η)
        (M:FundedPhysicalCatalogue.Purchase caps K F),
      FundedCoverKineticMeasurement.Tested R Y F M hG (fun v=>(0:(J.tests v).Mood)) →
      ∀ S:FundedRenderedBank.Chosen K I M.toCatalogue,
      η≤(Currency.g R.family z.cutoff z.period (z.level+1))^2 →
      I.carrier.rep.eval=(R.family.path.rep z.cutoff z.period (z.level+1)).eval →
      let O:=S.bank.output
      let Q:=onRun R z.cutoff z.period z.level O.model r
      let x:=(plan M.plan p).predict z.level+delta (S.vacuum.listing.read S.vacuum.source)
      let w:=fun v=>F.outputRadii v/F.kernelCosts v
      let f:=regulatorRun R.family z.cutoff z.period (z.level+1)
      ∀ (t:IndependentTests J.tests) (U:Config G (R.family.side z.level z.period)) (ρ:ℂ),
        let v:=testInclusion J.tests t
        let actual:=(O.output.leaf v).density U
        let lower:=Poly.pass (Q.read v (Currency.gain x) U)*(O.residual.leaf v).density U
        Poly.price w (ρ • (lower-actual))≤ε*f^((p:ℝ)+1-J.eta)*Poly.price w (ρ • actual) := by
  obtain ⟨D,hD,s,pay⟩:=QLocalPhysicalRetunedMeasurement.selected (Γ:=Γ) R hG hT readout caps A K hp hq r
  let C:=(2:ℝ)^caps.packetRank*(Fintype.card V:ℝ)*2*(rate (max caps.packetPower (r+2)))*(6*D)
  let e:=min (ε/2) 1
  have he:0<e:=lt_min (div_pos hε (by norm_num)) zero_lt_one
  filter_upwards [pay,absorb R hG A K C s p J.eta_pos he,
    (tendsto_add_atTop_nat 1).eventually (Currency.g_small hG R.makes 1 zero_lt_one)]
    with m paid cheap small z hz Y F η I M contact S hη hI
  subst m
  dsimp only
  intro t U ρ
  obtain ⟨-, -, receipt⟩:=paid z rfl Y F η I M contact S hη hI
  let f:=regulatorRun R.family z.cutoff z.period (z.level+1)
  let v:=testInclusion J.tests t
  let actual:=(S.bank.output.output.leaf v).density U
  let w:=fun i=>F.outputRadii i/F.kernelCosts i
  let c:= C*K.geometry z.level*A.admittedCost z.level^s*f^(p+1)
  let g:=f^((p:ℝ)+1-J.eta)
  have fp:0<f:=Currency.g_pos R.makes _ _ _ (Nat.succ_le_of_lt z.below)
  have gn:0≤g:=Real.rpow_nonneg fp.le _
  have g1:g≤1:=Real.rpow_le_one fp.le (small z.cutoff z.period (Nat.succ_le_of_lt z.below)).le
    (by
      have h : (2:ℝ)≤p := by exact_mod_cast hp
      linarith [J.eta_lt_half])
  have hc:c≤e*g:=cheap z.cutoff z.period z.below
  have c1:c≤1:=hc.trans ((mul_le_of_le_one_right he.le g1).trans (min_le_right _ _))
  have cap:=receipt t U
  have cost:MarkedPackets.uniformReadCost caps.packetRank (Fintype.card V)
      (K.geometry z.level*(1+1)*(rate (max caps.packetPower (r+2))*
        (6*(D*A.admittedCost z.level^s*f^(p+1)))))=c:=by
    unfold MarkedPackets.uniformReadCost c C
    ring
  rw [cost] at cap
  have coeff:2*c≤ε*g:=by
    calc
      _≤2*(e*g):=mul_le_mul_of_nonneg_left hc (by norm_num)
      _≤2*(ε/2*g):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (min_le_left _ _) gn) (by norm_num)
      _=_:=by ring
  rw [Poly.adapted,Poly.adapted]
  calc
    _≤‖ρ‖*(2*c*Poly.price w actual):=mul_le_mul_of_nonneg_left (cap c1) (norm_nonneg _)
    _≤‖ρ‖*(ε*g*Poly.price w actual):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right coeff
      (Poly.nonnegative (fun i=>div_pos (F.output_radius_positive i) (F.kernel_positive i)) _)) (norm_nonneg _)
    _=_:=by ring

end YM.Integration.QLocalPhysicalRetunedRate
