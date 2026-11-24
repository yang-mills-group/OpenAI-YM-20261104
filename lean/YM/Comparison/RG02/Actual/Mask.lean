import YM.Comparison.RG02.Integral.Comparison
import YM.Comparison.RG02.Integral.Healthy
import YM.Next.MULTISOURCE.Ends
/-!
# Real represented input on the actual windows

Proof-independent Rep. Keep all indicator partners in `X`. For arbitrary physical represented
 Π, display the all-good vs other contributions to that Table (the same `Push`). For the more
 detailed structured budgets (separately) one will in particular specialize to Multi.Pulse etc --
 bind its exponential + forced convention here and require K bounds on same Rep. No costs on
 marked coefficients except meas+L^1; `Credit` for convenient construction; all `Chart.transport`
 still open. Emphasize that exponential normalization only used as denominator of source **after**
 tag-sum. Inside window at a U where Rep eval nonzero one may algebraically stage an input log
 with denominator that same function. Do not confuse this per-U read with the output normalization
 by an integral. Use no hypothesis of formal smoothness of inherited e/multi-force.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Actual
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree YM.Push.SectorMeasure
open YM.Marker YM.Multi Order Next.SectorChange Integral
open YM.Extra.Trajectories (connected connected_quiet pass_connected)
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {P : Rep G f} {O : ChartRatio G}
    {V : Type} [DecidableEq V] {R : Census V}
-- absolute unnormalized marked density argument: Π.
structure Floor (P : Rep G f) (X : Lit R (Config G f)) : Prop where
    vacancy (y) : (X y).part R.quiet = Complex.ofReal (P.eval y)
    safe : Leaf.All X
    gauges : GaugeInvariant X

variable (X : Lit R (Config G f)) (K : Bulk.Kernel S P.clip P.path O) (W : Bulk.Colors R G f)
  (U : Config G f)
/-- Leading volume term included in numerical part. -/
def levelScalar (P : Rep G f) : ℝ := P.v*Fintype.card (Site f)
def remainderVac (g : ℝ) (P : Rep G f) := P.activities.additive P.p U - temperature g * W.vac g U

variable (F : Forest S.ratio) (g : ℝ)
section shiftVac
open UVNext.CouplingReset
variable {U}
lemma reindex (he : P.beta=temperature g) (hp : U∈Calm P.p) : P.exponent U=
    (levelScalar P-localClassic g U W P.clip P.path-loop P.path U) - remainderVac W U g P := by
  obtain ⟨h1,h2,-⟩:= unmasked_precision P.path P.clip hp;
  unfold Rep.exponent; rw [he,YM.Push.BetaTransport.channels_split,h1,h2]
  unfold remainderVac localClassic levelScalar; ring
lemma base_entry (he : P.beta=temperature g) (hp : U∈Calm P.p) : P.eval U=
    weight g (levelScalar P) U W P.clip P.path * Real.exp (-remainderVac W U g P) := by
   unfold Integral.weight Rep.eval; rw [reindex W g he hp,sub_eq_add_neg (b:=remainderVac ..),Real.exp_add (_-_-_),P.activities.gas_one _ hp,mul_one]
lemma healthy_live (hp : U∈Calm P.p) : 0<P.eval U:= by unfold Rep.eval; rw [P.activities.gas_one _ hp,mul_one]; exact Real.exp_pos _
end shiftVac
variable [Fintype V]

def markWeight (Q : Rep G f) (Y : Lit R (Config G f)) (U : Config G f) := connected ((Q.eval U:ℂ)⁻¹ • Y U)
def errorLog (g : ℝ) (P : Rep G f) := markWeight P X U - markedLog g U W

/-- Per-U, compare relative to the analytic generator, retaining rough input explicitly in both
 exponent contributions. Matters even before the integral. Any inherited `e_natural` and
 mask-payment/residual budgets require proving estimates on the second factor; term-index budgets
 absent from this purely algebraic identity. -/
lemma actual_mark (H : Floor P X) (he : P.beta=temperature g) (hp : U∈Calm P.p) :
    olderInput K g (levelScalar P) W X U = model g (levelScalar P) W K U *
       (Complex.ofReal (Real.exp (-remainderVac W U g P)) • Poly.pass (errorLog X W U g P)-1) := by
    have h0 : (P.eval U:ℂ)≠0 := by exact_mod_cast (healthy_live hp).ne'
    let Z := (P.eval U:ℂ)⁻¹ • X U
    have hZ : Z.part R.quiet=1 := by unfold Z; rw [Poly.part_smul,H.vacancy,inv_mul_cancel₀ h0]
    let L:= markedLog g U W
    let E:= errorLog X W U g P
    have hL:L.part R.quiet=0:= part_lit_quiet _
    have hE:E.part R.quiet=0:=by unfold E errorLog; rw [Extra.Trajectories.part_sub,(show (markedLog g U W).part _=0 from hL), markWeight,connected_quiet hZ,sub_zero]
    have hX:= show (P.eval U:ℂ) • Poly.pass (L+E)=X U from (by rw [show L+E=connected Z from add_sub_cancel _ _,pass_connected hZ]; unfold Z; rw [smul_smul,mul_inv_cancel₀ h0,one_smul])
    rw [mul_sub,mul_one]; unfold olderInput; rw [Pi.sub_apply, ← hX, Extra.Trajectories.pass_add hL hE]; apply congrArg (· - _) ?_
    rw [base_entry W g he hp]; unfold model; rw [Complex.ofReal_mul, smul_mul_smul_comm]

-- `star` operations/covariance not here. Use real_holding with explicit `X` from
-- representation proof. Good outside: split by real flags, no claim of smoothness there.
variable (A : Set (F.Slice G))
def passby := F.drape (G:=G) ⁻¹' (Calm P.p)
def failedFlags := ((passby (P:=P) F)ᶜ : Set (F.Slice G))
local notation "L" => Lit R (F.Slice G)
local notation "OZ"=> F.order G
variable (t : S.Choices) (x : fieldDir G c 1)
local notation "Z" => Actual.stack t (sample g x) (temperature g) X ∘ F.drape
local notation "zones" => zone K P.p F g x

omit [Fintype V] in
lemma passby_meas : MeasurableSet (passby (P:=P) F) := F.continuous_drape.measurable (calm_meas _)

omit [Fintype V] in
lemma flag_part (H : Floor P X) (hs : MeasurableSet A) (h : A ⊆ zones) :
    Good OZ ((failedFlags (P:=P) F).indicator Z) ∧ Good OZ (((passby (P:=P) F)\A).indicator Z) ∧
     charge OZ (outside F t g x A X)=charge OZ ((failedFlags (P:=P) F).indicator Z)+charge OZ (((passby (P:=P) F) \ A).indicator Z) := by
   let f := passby (P:=P) F; have he : A ⊆ f:=fun _ hx=> (h hx).2.1
   let g₁ := failedFlags (P:=P) F; let g₂:=f \ A
   have hw := good_slice F t (sample g x) (temperature g) K.branches H.safe
   have h1 : Good (OZ) (g₁.indicator Z) := hw.on_window (passby_meas (P:=P) F).compl
   have h2 : Good (OZ) (g₂.indicator Z) := hw.on_window ((passby_meas (P:=P) F).diff hs)
   refine ⟨h1,h2,?_⟩
   rw [← add_cost h1 h2]; congr 1
   ext1 i
   change Aᶜ.indicator Z i=g₁.indicator Z i+g₂.indicator Z i
   unfold g₁ g₂ failedFlags f; by_cases h:i∈A
   · have hh : i∈passby (P:=P) F:= he h; simp [*]
   by_cases h:i∈ passby (P:=P) F <;> simp [*]

variable {a A' B Δ υ : ℝ} (R)
-- Example prescribed Pulse; other tagged insertion APIs must use their own mask data. Different
-- Masks ok, but Floor needs full density incl partners.
lemma many_floor (P : Rep G f) (hP : P.Lawful a A' B Δ υ) (he : GaugeInvariant P.exponent)
    (D : Hot R→ Pulse G f) (u : ∀ i,GaugeInvariant (D i).1) (u' : ∀ i v,GaugeInvariant ((D i).2 v))
    (ha : ∀ i,Envelope (D i).1 ∧ ∀ v, Envelope ((D i).2 v)) : Floor P (many P R D) := by
    refine ⟨fun x=>floor_part P x hP.labels _ _ (part_lit_quiet _) (fun _=> part_lit_quiet _), throughJet P hP _ _ ?_ ?_,?_⟩
    · exact Leaf.sum _ _ fun k=> Leaf.insert_ (ha k).1 _
    · exact fun v=> Leaf.sum _ _ fun k=> Leaf.insert_ ((ha k).2 v) _
    intro g y; unfold many composeAt; unfold GaugeInvariant at *; simp_rw [he, u, u', gauge_flags, show ∀ j, incumbent P (gauge g y) j=_ from fun j=> (incumbent_legible P j hP.labels.forced).symmetry g y]

/-- Exponent convention at all-good flags, even for non-singleton Pulse rows. This is where
       `olderInput` has no forced gas contribution but keeps all path terms & actual marks.
      (Mismatch with supplied analytic generators lives in mark-vac remainders.) -/
lemma compose_healthy (P : Rep G f) (hU : U ∈ Calm P.p) (D : Hot R→ Pulse G f):
    many P R D U=(P.eval U:ℂ) • Poly.pass (lit R (fun i=> (D i).1 U)) := by
    -- via allJets: expand all disjoint drivers after retaining scalar once in the full product
    ext i; rw [Poly.part_smul, ← Cumulants.driven_pass, Cumulants.driven_part,Finset.mul_sum,allJets]; apply Finset.sum_congr rfl; intro j _; rw [Step.simple_all (parts R) P D U hU]; rfl
lemma many_log (P : Rep G f) (hU : U∈Calm P.p) (D : Hot R→ Pulse G f) :
    markWeight P (many P R D) U=lit R (fun i => (D i).1 U) := by
    have hi: (P.eval U:ℂ)≠0 := by exact_mod_cast (healthy_live hU).ne'
    unfold markWeight; rw [compose_healthy,smul_smul, inv_mul_cancel₀ hi, one_smul]; exact Cumulants.connected_pass (part_lit_quiet _); exact hU
end YM.Comparison.RG02.Actual
