import YM.OPE.Compatible.Spa.Laur
import YM.OPE.Compatible.Spa.Toon
/-!
# Flag representatives with a prescribed first component

Under the readout and decomposition hypotheses of `YM.OPE.Stroke.Earth`, take `e ≤ l + 1` and a vector in the sum of the grade-`e` flag and its `Sapling` submodule.
If the vector's phase-zero component belongs to the grade-`e` phase-zero flag, it has a flag representative with exactly that component and a residual in `Sapling`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic StageLight
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{p p':Clip}
variable {v v' b u:ℝ}
variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full
variable {X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
variable {Y:M→ℝ}{V:(i':M)→ Alps K T i (Y i')}{A':(i:ℕ)→ Submodule ℝ (Bead G l i)}{hq:1 ≤ Y}{hp:4 ≤ i}{U:Z.Ω M Y}
local notation "J!"=> Fin (l+1)
local notation "F!"=> Tracts G d τ
local notation "JΛ"=> Fin (l+1) -- use
open Pipes
local notation "Sγ"=> Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀)
private lemma residualInSup {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A B : Submodule ℝ E) {y p : E} (hy : y ∈ A ⊔ B) (hr : y - p ∈ B) : p ∈ A ⊔ B :=
  sub_sub_cancel y p ▸ (A ⊔ B).sub_mem hy (le_sup_right (a := A) hr)

private lemma addResiduals {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Submodule ℝ E) {y p q : E} (hp : y - p ∈ A) (hq : p - q ∈ A) : y - q ∈ A := by
  rw [show y - q = (y - p) + (p - q) by abel]
  exact A.add_mem hp hq

private lemma firstReadTrim (U : Z.Ω M Y) (e : J!) (v : M) (p : U.flag e.val v)
    (y : F!) (h0 : p.val 0 = y 0) (hy : y 0 ∈ (Drift.Turns D₀ 0).flag (e.val + 1)) :
    trims 1 (U.read e.val e.isLt v p).val := by
  apply (bridgeV Z 1 (by decide) e.isLt (U.read e.val e.isLt v p)).2
  intro j hj
  have hj0 : j = 0 := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj))
  subst j
  rw [vintage Z U e.isLt v p 0 (trims.be _), h0]
  exact (((Drift.Turns D₀ 0).next e.val e.isLt _).mp hy).2

private lemma successorRepresentative {κ : (e : J!) → Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)}
    (U : Z.Ω M Y) (hX : ∀ j, (V j).clip = p') (T' : Z.Floss V U hp (le_trans zero_le_one hq) k Hp a)
    (C : Bals Hp Z a A' κ) (hx : l*l ≤ τ 0) (X' : Lance X) (e : J!) (v : M) (p : U.flag e.val v)
    (hp' : ReadK Z κ U e v p = 0) (ht : trims 1 (U.read e.val e.isLt v p).val) :
    ∃ q : U.flag (e.val + 1) v, p.val - q.val ∈ Sγ v ∧ trims 1 (p.val - q.val) := by
  obtain ⟨q, _, hv⟩ := BayFin (hq:=hq) Hp Z a U hX T' C hx X' e (fun _ : Unit => v) 1
    zero_le_one (fun _ => p) (wealthC p.val) (fun _ => hp') 1 (fun _ => ht)
  exact ⟨q (), hv ()⟩

set_option maxHeartbeats 200000 in
lemma Earth {κ:(e:J!)→Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)} (U:Z.Ω M Y)(hX:∀ j,(V j).clip=p')(T': Z.Floss V U hp (le_trans zero_le_one hq) k Hp a)(C:Bals Hp Z a A' κ)(hx:l*l≤τ 0)(X':Lance X)(e:ℕ)(he:e ≤ l+1)(v:M)(y:F!)(hz:y∈Bay U.flag Sγ e v)(h:y (0:Phase)∈ (Drift.Turns D₀ 0).flag e):∃ p:U.flag e v, y-p.val∈ Sγ v ∧ p.val 0=y 0:=by

  let W := Drift.Turns D₀ 0
  induction e with
  | zero =>
    let p : U.flag 0 v := ⟨y, U.first v |>.symm ▸ Submodule.mem_top⟩
    exact ⟨p, show y - y ∈ Sγ v from (sub_self y).symm ▸ Submodule.zero_mem _, rfl⟩
  | succ t ih =>
    let i : Fin (l + 1) := ⟨t, he⟩
    obtain ⟨p, hP, h0⟩ := ih (Nat.le_trans (Nat.le_succ t) he)
      (sup_le_sup_right (U.moves t v he) (Sγ v) hz) (((W.next t he _).mp h).1)
    have hp' : ReadK Z κ U i v p = 0 :=
      deepRun (V:=V) (hq:=hq) Hp Z a C U T' i v p
        (residualInSup (U.flag (t+1) v) (Sγ v) hz hP)
    obtain ⟨q, hq', ht⟩ := successorRepresentative Hp Z a U hX T' C hx X' i v p hp'
      (firstReadTrim Z U i v p y h0 h)
    have same : p.val 0 = q.val 0 := sub_eq_zero.mp (ht (0 : Phase) (by decide))
    exact ⟨q, addResiduals (Sγ v) hP hq', same.symm.trans h0⟩
end YM.OPE.Stroke
