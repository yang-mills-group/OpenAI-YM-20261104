import YM.Integration.WilsonRootedKioskFreeRadius
import YM.Integration.WilsonRootedKioskPostedPortfolio
import YM.Integration.WilsonPhysicalHistoryKioskGraduate

/-! On the original physical two-merger walk, subtract the entire admitted
unmasked model before the true second tap at the recorded coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedKioskPhysicalPostWhole
open Function Finset Lattice Wilson RG Source Pressure Ac Marker Push.Corrected Push.AbsoluteSums
open PhysicalNext PhysicalNext.Repeat Progress.DirectedRecipe RemainderComparison
open QuadraticLocal QuadraticLocal.Travel QuadraticLocal.Trigger ConnectedActivityE6 Lyric Muse Serif Spire
open Merge Lotus Typeface MeasureTheory WilsonPhysicalHistoryPictureRestore
open scoped Classical BigOperators

open Filter IterationFour PhysicalNext.Repeat.Legato Pert.Asymptotics OPE.Therm


variable {G : Gauge} (X : Run G) 
  {I V : Type} [Countable I] [DecidableEq V] [Fintype V]
  {N per i : ℕ} {L : Side} {T : Type}
  {x e f r s κ w b₀ b₁ z Y Γ K : ℝ} {A₀ : Teller G} {Q : ConnectedActivityE6.Target G A₀}
  {horizon : ConnectedActivityE6.Target.Order G w}
  {tube : Pressure.Tube G (X.family.path.levels.clock.op i per)}
  {P : Rep G (X.family.side (i+1) per)} {P' : Rep G (X.family.side i per)}
  (cash : Cash w x κ L Q horizon z tube P) {k : ℕ} (eyes : Eyes cash P' e Γ Y K k)
  (W : Travel.Walk cash P' e f r s)
  {R : Census V} {o : V → Site (X.family.side (i+1) per)}
  (A : Gallery T I o P R) (weights : V → ℝ) (grant : Seal A weights b₀ b₁)
  (pos : ∀ v,0<weights v) (slots : HasSlots P.p P.activities)
  (cap : ∀ m : R.Mode,m.val.card ≤ k) (bill : 2*(b₀+b₁) ≤ K) (pin : T)


open WilsonRootedKioskOccupiedSlip WilsonRootedKioskSlipCharge
open QuadraticLocal.Shelter

variable {J E I₀:Type}[Countable J][Countable E]
  (L₀:Lamps T J G P'.p ((X.family.path.levels.clock.op i per).ratio.parent ∘ o) R)(S:Lamps T I₀ G P'.p ((X.family.path.levels.clock.op i per).ratio.parent ∘ o) R)(M:Canopy.ShiftRows T E G P'.p ((X.family.path.levels.clock.op i per).ratio.parent ∘ o) R)

theorem original (live:i<N)
    (fineView:P.eval=(X.family.path.rep N per (i+1)).eval)
    (temperature:P.beta=(X.family.path.rep N per (i+1)).beta)
    (coarseView:P'.eval=(X.family.path.rep N per i).eval)
    (outputBeta:P'.beta=(X.family.path.rep N per i).beta)
    (point:P'.p=(X.family.path.rep N per i).p)
    {B_s C_s M_D:ℝ}(residual:S.Paid weights P'.p.B (P'.p.supportExponent) B_s)
    (existing:M.Budget weights P'.p.B ((P'.p.supportExponent)+1) C_s)
    (unmasked:Gross L₀ weights P'.p.B ((P'.p.supportExponent)+1) M_D)(slack:0<s)(shrink:ℝ)
    (lines:∀t u,(Travel.raw cash eyes A weights grant pos slots bill pin).log t u=L₀.log t u+S.log t u+M.log t u)
    (forest:Tree.Forest (X.family.path.levels.clock.op i per).ratio):
    let h:=WilsonRootedKioskFreeRadius.radius shrink C_s M_D s
    let u:=Stoop.radius weights h
    let O:=WilsonRootedKioskPostedPortfolio.residual (Travel.mid cash W eyes A weights grant pos slots cap bill pin) W.second L₀ S M
    1 ≤ h ∧ shrink ≤ h ∧ O.Pays u (P'.p.supportExponent) (h⁻¹*B_s) r ∧
    (∀t z,O.density t z=Poly.pass (-(bare L₀ t z))*(X.family.path.levels.clock.op i per).push (X.family.path.rep N per (i+1)).beta (A.density t) z) ∧
    (∀t z,(O.density t z).part R.quiet=((X.family.path.rep N per i).eval z:ℂ)) ∧
    P'.beta=(X.family.path.rep N per i).beta ∧ P'.p=(X.family.path.rep N per i).p:=by
  intro h u O
  have one:1 ≤ h:=(le_max_left 1 shrink).trans (le_max_left _ _)
  have reserved:shrink ≤ h:=(le_max_right 1 shrink).trans (le_max_left _ _)
  have ledger:(C_s+M_D)/s ≤ h:=le_max_right _ _
  have total:h⁻¹*C_s+h⁻¹*M_D ≤ s:=by
    rw [←mul_add,mul_comm,←div_eq_mul_inv]
    exact (div_le_iff₀ (zero_lt_one.trans_le one)).mpr (by simpa only [mul_comm] using (div_le_iff₀ slack).mp ledger)
  have up(v):0<u v:=div_pos (pos v) (zero_lt_one.trans_le one)
  obtain ⟨rawPaid,hardPaid,observed⟩:=Travel.docket cash W eyes A weights grant pos slots cap bill pin forest
  let early:=fun t=>(X.family.path.levels.clock.op i per).push P.beta (A.density t)
  have ht:0≤(P'.p.supportExponent)+1+1:=by linarith [P'.p.exponent_pos]
  have first0 (t) (z):(early t z).part R.quiet=(P'.eval z:ℂ):=by
    rw [coarseView]
    change ((X.family.path.levels.clock.op i per).push P.beta (A.density t) z).part R.quiet=_
    rw [Travel.tuneQuiet cash eyes A weights grant pos slots cap bill pin t z,temperature,fineView]
    exact congrArg Complex.ofReal (congrFun (X.makes.wilson.steps N per i live).1 z).symm
  have positive(z):P'.eval z≠0:=by
    rw [coarseView];exact (Multi.AxisShift.chosen_positive X.makes.wilson live.le z).ne'
  have phase:=WilsonRootedKioskFreeRadius.moved M pos one existing
  have added:=WilsonRootedKioskSlipCharge.cost L₀ pos one unmasked
  have done:=WilsonRootedKioskPostedPortfolio.received (Travel.mid cash W eyes A weights grant pos slots cap bill pin) W.second L₀ S M u up P'.p.exponent_pos.le
    (Stoop.leaves weights (Travel.mid cash W eyes A weights grant pos slots cap bill pin) pos one hardPaid) (Stoop.tighten weights S pos one residual)
    phase added total early (Travel.raw cash eyes A weights grant pos slots bill pin).log observed lines pos (by linarith [P'.p.exponent_pos]) unmasked
    (fun t z=>Lamps.quiet_of_hasSum t z (rawPaid.sums ht pos t z)) first0 positive
  refine ⟨one,reserved,done.1,fun t z=>?_,fun t z=>?_,outputBeta,point⟩
  · rw [←temperature];exact (congrFun (done.2.1 t) z).symm
  · exact (done.2.2 t z).trans (congrArg Complex.ofReal (congrFun coarseView z))

end YM.Integration.WilsonRootedKioskPhysicalPostWhole
