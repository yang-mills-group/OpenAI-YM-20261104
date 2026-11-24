import YM.OPE.Compatible.Mould.Cover
/-! # currency.MainSap transfer. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}
variable {H:LocalRatio R}{hs:G.Simple}{X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m){Z:Topic H hs X B D₀}{a:Axis}
open Flume.Script Maxwell Balsam Nestle Pert.Full -- don't open Variance.Gift
variable {p₁:Clip}{u vν ν:M→ℝ}{hp:4≤ i}{V:(j:M)→Alps K T i (u j)}{hq:1 ≤ u}{U: Z.Ω M u}
local notation "F!"=> Tracts G d τ
variable (T': Z.Floss V U hp (le_trans zero_le_one hq) k Hp a)
local notation "Ω!"=> Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀)
noncomputable def Shifts (G:Gauge)(h:Aware d τ)(i:Phase)(z:Tracts G d τ):= (fun i=> Quit.Jac.Gift G h i)^[i.val] z
lemma shotT (p:F!)(i j:Phase)(hp:i.val+1=j.val)(h:Aware d τ): Shifts G h j p=Quit.Jac.Gift G h (Shifts G h i p):=by
      unfold Shifts; rw[←hp, iterate_succ_apply']
lemma trimS (p:F!)(i:Phase)(h:Aware d τ): trims i.val (Shifts G h i p) :=by
      have ht:trims 1 (Gift G h p):= trims.up (0:Phase) (trims.be _) (tack ..)
      have hv:trims 1 (Gift G h (Gift G h p)):=trims.up (0:Phase) (trims.be _) (tack ..)
      fin_cases i; · exact trims.be _
      · exact ht
      exact trims.up (1:Phase) hv (by change Gift G h (Gift G h p) 1=0; rw[tack1 h (Gift G h p) 0 1 rfl,ht 0 (by decide),map_zero]) -- annotations
lemma cashU (he:e<l+1)(z:M→Mint Z e)(hz: Wealth (fun i=>(z i).val) u ν)(j:Phase): Wealth (fun i=>UΦ Z he (z i) j) u ν:=aimW ((Drift.Turns D₀ j).Tap e) (aimW (ContinuousLinearMap.proj (R:=ℝ) j) hz)
include T'
lemma boosts (he:e <l+1)(p:∀ i,U.flag e i)(hz:Wealth (fun i=>(p i).val) u ν)(hx:∀ i,(p i).val∈ Ω! i):∃ v:∀ i,U.flag e i, Wealth (fun i=>(v i).val) u ν∧ (∀ i,(v i).val∈ Ω! i) ∧ ∀ i,(v i).val=Gift G D₀.aware (p i).val∧ U.read e he i (v i)= WaneZ Z e he (U.read e he i (p i)) :=by
     choose v h H' using fun i=> T'.turn e he i (p i); have K(i:M):(v i).val∈Ω! i:=by rw [show (v i).val=_ from h i]; exact sapUp (D₀:=D₀) a hp _ (hx i)
     refine ⟨v,?_,K,fun i=>⟨h i,H' i⟩⟩; simp_rw[h]; exact aimW (Gift G D₀.aware) hz
omit T'

private def liftedPhase (p : ∀ i, U.flag e i) (he : e < l + 1) (j : Phase) : Prop :=
  ∃ v : ∀ i, U.flag e i, Wealth (fun i => (v i).val) u ν ∧
    (∀ i, (v i).val ∈ Ω! i) ∧ ∀ i, (v i).val = Shifts G D₀.aware j (p i).val ∧
      UΦ Z he (U.read e he i (v i)) j = UΦ Z he (U.read e he i (p i)) 0

local notation "Lifted" => liftedPhase (hq := hq) (Z := Z) (a := a) (V := V) (U := U) (hp := hp) (ν := ν)

private lemma nextValue (h : Aware d τ) (j k : Phase) (adj : j.val + 1 = k.val)
    {x v w : Tracts G d τ} (step : w = Quit.Jac.Gift G h v) (prev : v = Shifts G h j x) :
    w = Shifts G h k x :=
  step.trans ((congrArg (Quit.Jac.Gift G h) prev).trans (shotT x j k adj h).symm)

private lemma nextReading (he : e < l+1) (j k : Phase) (adj : j.val + 1 = k.val)
    {v w base : Mint Z e} (step : w = WaneZ Z e he v)
    (prev : UΦ Z he v j = UΦ Z he base 0) : UΦ Z he w k = UΦ Z he base 0 :=
  (congrArg (fun x => UΦ Z he x k) step).trans ((riseΦ Z he v j k adj).trans prev)

include T'

private lemma liftNext (p : ∀ i, U.flag e i) (he : e < l + 1)
    (j k : Phase) (adj : j.val + 1 = k.val) (current : Lifted p he j) : Lifted p he k := by
  obtain ⟨v, rich, member, previous⟩ := current
  obtain ⟨w, richer, inside, turn⟩ := boosts (hq := hq) Hp T' he v rich member
  refine ⟨w, richer, inside, fun i => ?_⟩
  exact ⟨nextValue D₀.aware j k adj (turn i).1 (previous i).1,
    nextReading (Z := Z) he j k adj (turn i).2 (previous i).2⟩

omit T'

private lemma allPhases (F : Phase → Prop) (zero : F 0)
    (step : ∀ i j : Phase, i.val + 1 = j.val → F i → F j) (j : Phase) : F j := by
  have one := step 0 1 rfl zero
  have two := step 1 2 rfl one
  fin_cases j <;> assumption

include T'

private lemma attainPhases (p : ∀ i, U.flag e i) (he : e < l + 1)
    (rich : Wealth (fun i => (p i).val) u ν) (member : ∀ i, (p i).val ∈ Ω! i)
    (j : Phase) : Lifted p he j :=
  allPhases (fun i => Lifted p he i) ⟨p, rich, member, fun _ => ⟨rfl, rfl⟩⟩
    (liftNext (hq := hq) Hp T' p he) j

lemma Streaks (p:∀ i,U.flag e i)(he:e<l+1)(hv:Wealth (fun i=>(p i).val) u ν)(hp:∀ i,(p i).val∈ Ω! i)(j:Phase):∃ v:∀ i,U.flag e i, Wealth (fun i=>(v i).val) u ν ∧ (∀ i,(v i).val∈ Ω! i) ∧∀ i,(v i).val=Shifts G D₀.aware j (p i).val∧ UΦ Z he (U.read e he i (v i)) j=UΦ Z he (U.read e he i (p i)) 0 :=by
  exact attainPhases (hq := hq) Hp T' p he hv hp j
end YM.OPE.Stroke
