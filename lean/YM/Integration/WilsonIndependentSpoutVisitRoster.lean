import YM.Integration.WilsonIndependentSpoutFittedRosterExit
import YM.Integration.WilsonIndependentSpoutVisitWallet

/-! The true normalized Wilson return is uniform in the finite family of positions visited on each prescribed board. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutVisitRoster
open Lattice RG Source Labels PertExtension XSpace XSpace.Rose XSpace.Cirrus Precision
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Mer
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Cluster RegulatorIR.Prim RegulatorIR.Gain RegulatorIR.Halo RegulatorIR.Taping
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Uniform RegulatorIR.Oracle RegulatorIR.Atlas
open RegulatorIR.Epoch RegulatorIR.Epoch.League RegulatorIR.Momentum RegulatorIR.Profiles RegulatorIR.Calibration
open WilsonIndependentExactPlate WilsonIndependentLicensedCircuit WilsonIndependentRawRosterWord
open WilsonIndependentSpoutFittedRosterExit (raw returned)
open scoped Classical BigOperators
variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)(K:KernelChoices)
    (Y:Program K)(Z:∀P:Patch,P.Branches K G)(V:XSpace.Run)(a j:ℕ)(ha:0<a)(late:4≤j)
    (A:Requests a → Levels G)(s:Requests a → ℕ)(D:Tent (M V a))(p:ℕ)
variable {I T:Type}[Fintype T](σ:T → I → Bool)(d:I → ℕ)(key:T → (i:I)→(R.family.labels.level (d i)).Index)
    {E:I → ℕ}(cut:∀i,d i<E i)(arms:Composite I)(sample:Requests a → Sample 2)
variable {B:Requests a → Type}[∀w,Fintype (B w)][∀w,Nonempty (B w)]
    (sites:(w:Requests a) → B w → I → Cover)(center:(w:Requests a) → B w → Room)

theorem convolution {L:Type}[Fintype L](q:ℕ)(ω z:L → PowerSeries ℂ):
    PowerSeries.coeff q (∑t,ω t*z t)=∑i:L × Fin (q+1),
      PowerSeries.coeff i.2.val (ω i.1)*PowerSeries.coeff (q-i.2.val) (z i.1):=by
  rw [map_sum,Fintype.sum_prod_type]
  simp only [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.sum_range]

theorem original (simple:G.Simple)(O:ChartRatio G)(ratio:LocalRatio O)(γ:ℝ)(ap:Requests a → ℝ)
    (priced:WilsonIndependentPublicRosterBook.Priced R W K Y Z V a j ha late p γ ap D)
    (read:∀f,WilsonIndependentNotebookMarkedEdge.Reads (S V a ha j late) Y Z D A s p f)
    (c₀:ℝ)(board:∀w,(sample w).F=V.step w.val)
    (reach:∀w b,WilsonIndependentRawRosterBudget.span (center w b) (sites w b) arms≤ap w)(small:0<c₀)
    (safe:∀pick:∀w,B w,((S V a ha j late).dialect Y G Z (sheet D)).cushion c₀ (fun w=>center w (pick w)))
    (q:ℕ)(hq:q≤p):
    ∃k:ℕ,∃H:ℝ,0≤H ∧ ∀(w:Requests a)(L:Type)[Fintype L](v:L → B w)(t:L → T)(ω:L → PowerSeries ℂ),
      ‖PowerSeries.coeff q (∑i,ω i*raw R W a σ d key arms sample (fun _=>sites w (v i)) w (t i))-
        PowerSeries.coeff q (∑i,ω i*returned R W V a A s σ d key cut arms (fun _=>sites w (v i)) O w (t i))‖≤
        (∑z:L × Fin (q+1),‖PowerSeries.coeff z.2.val (ω z.1)‖) *
        (H*(1+ap w+Real.log ((V.step w.val).p.side.val:ℝ))^k*((V.step w.val).p.side.val:ℝ)^(-(γ/2))):=by
  let width (w:Requests a):ℝ:=1+ap w+Real.log ((V.step w.val).p.side.val:ℝ)
  let tail (w:Requests a):ℝ:=((V.step w.val).p.side.val:ℝ)^(-(γ/2))
  let X (w:Requests a)(b:B w)(z:T × Fin (q+1)):=PowerSeries.coeff (q-z.2.val)
    (raw R W a σ d key arms sample (fun _=>sites w b) w z.1)
  let U (w:Requests a)(b:B w)(z:T × Fin (q+1)):=PowerSeries.coeff (q-z.2.val)
    (returned R W V a A s σ d key cut arms (fun _=>sites w b) O w z.1)
  have one (w:Requests a):1≤width w:=by
    let b:B w:=Classical.choice inferInstance
    have hp:=(WilsonIndependentRawRosterBudget.extent (center w b) (sites w b) arms).trans (reach w b)
    have hn:1≤((V.step w.val).p.side.val:ℝ):=by exact_mod_cast (V.step w.val).p.side.pos
    have hlog:=Real.log_nonneg hn
    dsimp only [width]
    linarith
  have bill (z:T × Fin (q+1))(pick:∀w,B w):∃k:ℕ,∃H:ℝ,0≤H ∧ ∀w,
      ‖X w (pick w) z-U w (pick w) z‖≤H*(width w)^k*tail w:=by
    simpa only [X,U,raw,returned,PowerSeries.coeff_mk,width,tail] using
      WilsonIndependentSpoutEnrolledRosterExit.original R W K Y Z V a j ha late A s D p simple O ratio γ ap priced read
      I (σ z.1) d (key z.1) cut arms sample (fun w=>sites w (pick w)) (fun w=>center w (pick w)) c₀ board
      (fun w=>reach w (pick w)) small (safe pick) (q-z.2.val) (by omega)
  obtain ⟨k,H,pos,paid⟩:=WilsonIndependentSpoutVisitWallet.original width tail one
    (fun w=>Real.rpow_nonneg (Nat.cast_nonneg _) _) X U bill
  refine ⟨k,H,pos,?_⟩
  intro w L _ v t ω
  rw [convolution,convolution]
  exact WilsonIndependentSpoutVisitWallet.applied _ (fun z:L × Fin (q+1)=>X w (v z.1) (t z.1,z.2))
    (fun z=>U w (v z.1) (t z.1,z.2)) (fun z=>paid w _ _) (fun z=>PowerSeries.coeff z.2.val (ω z.1))

end YM.Integration.WilsonIndependentSpoutVisitRoster
