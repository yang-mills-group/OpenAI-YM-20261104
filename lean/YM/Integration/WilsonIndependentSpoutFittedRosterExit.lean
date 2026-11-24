import YM.Integration.WilsonIndependentSpoutEnrolledRosterExit
import YM.Integration.WilsonIndependentSpoutOrbitLedger

/-! Cleared thermal fits, at their own regulators, on the normalized physical orbit and the full dated returns of the same submitted basis. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutFittedRosterExit
open Lattice RG Source Labels PertExtension XSpace XSpace.Rose XSpace.Cirrus Precision
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Mer
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Cluster RegulatorIR.Prim RegulatorIR.Gain RegulatorIR.Halo RegulatorIR.Taping
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Uniform RegulatorIR.Oracle RegulatorIR.Atlas
open RegulatorIR.Epoch RegulatorIR.Epoch.League RegulatorIR.Momentum RegulatorIR.Profiles RegulatorIR.Calibration
open WilsonIndependentExactPlate WilsonIndependentLicensedCircuit WilsonIndependentRawRosterWord
open WilsonIndependentMatchedOpeningRoster (field)
open scoped Classical
variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)(K:KernelChoices)
    (Y:Program K)(Z:∀P:Patch,P.Branches K G)(V:XSpace.Run)(a j:ℕ)(ha:0<a)(late:4≤j)
    (A:Requests a → Levels G)(s:Requests a → ℕ)(D:Tent (M V a))(p:ℕ)

variable {I T:Type}[Fintype T] (σ:T → I → Bool)(d:I → ℕ)(key:T → (i:I) → (R.family.labels.level (d i)).Index)
    {E:I → ℕ}(cut:∀i,d i<E i)(arms:Composite I)(sample:Requests a → Sample 2)(sites:Requests a → I → Cover)

def raw (w:Requests a)(t:T):PowerSeries ℂ:=
  Bare.normalized (W.tree (sample w).F.p) G (film R W (σ t) d (key t) (sample w) (sites w) arms)

def returned (O:ChartRatio G)(w:Requests a)(t:T):PowerSeries ℂ:=
  PowerSeries.mk fun q=>(note (WilsonIndependentSpoutOriginalMarkedJourney.source A s O (Page.finallyW (M V a) w)
    (cruises (A w) O (s w+M V a w) (arms.accounts (degree R d (key t))) (s w+M V a w) (s w)
      (field R W (σ t) d (key t) cut (sites w) arms)) q 0):ℂ)

private theorem convolution (q:ℕ)(w z:T → PowerSeries ℂ):
    PowerSeries.coeff q (∑t,w t*z t)=∑i:T × Fin (q+1),
      PowerSeries.coeff i.2.val (w i.1)*PowerSeries.coeff (q-i.2.val) (z i.1):=by
  rw [map_sum,Fintype.sum_prod_type]
  simp only [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.sum_range]

theorem original (simple:G.Simple)(O:ChartRatio G)(ratio:LocalRatio O)(γ:ℝ)(ap:Requests a → ℝ)
    (priced:WilsonIndependentPublicRosterBook.Priced R W K Y Z V a j ha late p γ ap D)
    (read:∀f,WilsonIndependentNotebookMarkedEdge.Reads (S V a ha j late) Y Z D A s p f)
    (x:Requests a → Room)(c₀:ℝ)(board:∀w,(sample w).F=V.step w.val)
    (reach:∀w,WilsonIndependentRawRosterBudget.span (x w) (sites w) arms≤ap w)(small:0<c₀)
    (safe:((S V a ha j late).dialect Y G Z (sheet D)).cushion c₀ x)(q:ℕ)(hq:q≤p):
    ∃k:ℕ,∃H:ℝ,0≤H ∧ ∀(weight:Requests a → T → PowerSeries ℂ)(w:Requests a),
      ‖PowerSeries.coeff q (∑t,weight w t*raw R W a σ d key arms sample sites w t)-
        PowerSeries.coeff q (∑t,weight w t*returned R W V a A s σ d key cut arms sites O w t)‖≤
        (∑z:T × Fin (q+1),‖PowerSeries.coeff z.2.val (weight w z.1)‖)*
          (H*(1+ap w+Real.log ((V.step w.val).p.side.val:ℝ))^k*((V.step w.val).p.side.val:ℝ)^(-(γ/2))):=by
  let width (w:Requests a):ℝ:=1+ap w+Real.log ((V.step w.val).p.side.val:ℝ)
  let tail (w:Requests a):ℝ:=((V.step w.val).p.side.val:ℝ)^(-(γ/2))
  let L (w:Requests a)(z:T × Fin (q+1)):=PowerSeries.coeff (q-z.2.val) (raw R W a σ d key arms sample sites w z.1)
  let U (w:Requests a)(z:T × Fin (q+1)):=PowerSeries.coeff (q-z.2.val) (returned R W V a A s σ d key cut arms sites O w z.1)
  have one (w:Requests a):1≤width w:=by
    have hp:= (WilsonIndependentRawRosterBudget.extent (x w) (sites w) arms).trans (reach w)
    have hn:1≤((V.step w.val).p.side.val:ℝ):=by exact_mod_cast (V.step w.val).p.side.pos
    have hlog:=Real.log_nonneg hn
    dsimp only [width]
    linarith
  have bill (z:T × Fin (q+1)):∃k:ℕ,∃H:ℝ,0≤H ∧ ∀w,‖L w z-U w z‖≤H*(width w)^k*tail w:=by
    simpa only [L,U,raw,returned,PowerSeries.coeff_mk,width,tail] using
      WilsonIndependentSpoutEnrolledRosterExit.original R W K Y Z V a j ha late A s D p simple O ratio γ ap priced read
        I (σ z.1) d (key z.1) cut arms sample sites x c₀ board reach small safe (q-z.2.val) (by omega)
  obtain ⟨k,H,pos,earned⟩:=WilsonIndependentSpoutOrbitLedger.original width tail one
    (fun w=>Real.rpow_nonneg (Nat.cast_nonneg _) _) L U bill
  refine ⟨k,H,pos,fun weight w=>?_⟩
  rw [convolution,convolution]
  exact earned (fun w z=>PowerSeries.coeff z.2.val (weight w z.1)) w

end YM.Integration.WilsonIndependentSpoutFittedRosterExit
