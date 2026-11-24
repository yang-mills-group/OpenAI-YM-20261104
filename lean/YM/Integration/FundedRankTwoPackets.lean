import YM.WilsonCoeffUV.Reclosure.TaylorLift
import YM.Comparison.Density.Render.Weld
import YM.IterationFour.Vacuum.Payload

/-! Turn the paid two-plaquette moments into the actual rooted affine-null
physical payloads and the exact native charge on failed enlarged masks. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FundedRankTwoPackets
open Function Filter Finset Lattice Wilson RG
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open Extra.Iteration WilsonStartup AnalyticBridge.VerifiedReset
open Comparison.Density Comparison.Density.Render
open Comparison.Density.Fusing Comparison.Density.Markers Comparison.Density.Registers Marker
open Progress.DirectedRecipe AnalyticBridge.VerifiedReset.Collection
open IterationFour.Vacuum
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} {n : Side} {σ C : ℝ}

private def tensor (i : Fin 2 → PlaqAxes) (x : Fin 2 → G.ColorIndex) (w : AnalyticBridge.VerifiedReset.Flux G) :=
  ∏ j, (w (i j)) (x j)

private theorem reading (P : Stack G 0) (k : ℕ) (w : AnalyticBridge.VerifiedReset.Flux G) :
    Render.tag (P k) w =
      ∑ i : Fin 2 → PlaqAxes, ∑ x : Fin 2 → G.ColorIndex, silentPay P i x k * tensor i x w := by
  classical
  let d := fun j => ((P k).leg j).plaq
  calc
    _ = ∑ i : Fin 2 → PlaqAxes,
        if d=i then ∑ x : Fin 2 → G.ColorIndex,(P k).coeff x * tensor i x w else 0 := by
      simp [Render.tag,Atom.poly,tensor,d]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : (fun j => ((P k).leg j).plaq)=i <;> simp [silentPay,d,hi]

theorem central (P : Stack G 0) (hP : Sprite P) : Frame.Central P := by
  intro w
  have h : HasSum
      (fun k => ∑ i : Fin 2 → PlaqAxes, ∑ x : Fin 2 → G.ColorIndex, silentPay P i x k * tensor i x w)
      (∑ i : Fin 2 → PlaqAxes, ∑ x : Fin 2 → G.ColorIndex, (0:ℝ) * tensor i x w) :=
    hasSum_sum fun i _ => hasSum_sum fun x _ => ((hP i x).1).mul_right _
  simpa only [reading,zero_mul,Finset.sum_const_zero] using h

theorem signed (P : Stack G 0) (hP : Sprite P) : Frame.SignedCentral P := by
  intro w
  simpa only [Finset.sum_const_zero] using
    (hasSum_sum (s:=Finset.univ) (fun t (_ : t ∈ (Finset.univ : Finset Signed)) =>
      central P hP (reframe w t)))

theorem funded {d : ℕ} (P : Stack G 0) (hP : Commission P σ C d) (hd : 0 < d) :
    Frame.SignedCentral P := signed P (hP.loan hd)

def payload (P : Stack G 0) (n : Side) (q : ℝ) : Payload G n where
  labels := (Frame.makeRose P n q Frame.full).shelf ∘ numbering (Cycle n)
  action := (Frame.makeRose P n q Frame.full).table ∘ numbering (Cycle n)

theorem invoice {d : ℕ} (P : Stack G 0) (hP : Commission P σ C d) (hG : G.Simple)
    (hn : 20 < n.val) (q : ℝ) (B : BudgetPoint) (hσ : 0 < σ)
    (hB : B.supportExponent / B.B ≤ σ/4) (hc : 2 ≤ B.B)
    (A : Activities G n) (hA : ∀ t b,A.Moves t b) :
    (payload P n q).Invoice B (Frame.cost B * (Frame.roseCharge q σ G B*C)) := by
  let F := Frame.makeRose P n q Frame.full
  have H := Frame.rose_era P n q Frame.full hP.hue B
  have N := Frame.rose_stars P n q hG Frame.full hP.hue B hn
  have R := Frame.authentic A H N hG (by omega)
  have E := Frame.economics A H (Frame.in_time P n q hσ hB hc Frame.full hP.toll)
  refine ⟨R.smooth,R.at_flat,R.vanish,?_,E⟩
  intro t b
  let m := Frame.move F A (hA t b)
  exact ⟨m.ep,fun i => ⟨m.reg_site i,m.reg_support i,m.valuesE i⟩⟩

theorem all_fields {d : ℕ} (P : Stack G 0) (hP : Commission P σ C d) (hd : 0 < d)
    (q : ℝ) (B : BudgetPoint) (hσ : 0 < σ) (hB : B.supportExponent / B.B ≤ σ/4)
    (hc : 2 ≤ B.B) (A : Activities G n) (V : Type) [DecidableEq V]
    (R : Census V) (X : V → Type) (U : Config G n) :
    (∑' i,(Frame.pours P B q V R X).real.value i U) =
      (payload P n q).amount B U - ((Render.rack n P q Frame.full).coffee A).additive B U :=
  Frame.pays P q hP.hue hP.toll hσ hB hc A (funded P hP hd) U

theorem compensated {d : ℕ} (P : Stack G 0) (hP : Commission P σ C d)
    (q : ℝ) (B : BudgetPoint) (hσ : 0 < σ) (e : ℝ) (he : 0 ≤ e)
    (hB : (later B (e+2) (by linarith)).supportExponent / B.B ≤ σ/4) (hc : 2 ≤ B.B)
    {V : Type} [DecidableEq V] {R : Census V} {X : V → Type}
    [∀ v,NormedAddCommGroup (X v)] [∀ v,NormedSpace ℂ (X v)]
    (O : Readers V X n) (w : V→ℝ) :
    let D := later B (e+2) (show 0 ≤ e+2 by linarith)
    let z := Frame.cost D * (Frame.roseCharge q σ G D*C)
    Placed B O (Frame.pours P B q V R X) ∧
      Compensated B O (Frame.pours P B q V R X) w e
        (YM.Push.AbsoluteSums.Footprint.payment 1 (4*B.B+2) 0 1 (2/(turnFee D)) z (B.supportExponent+e) 0) := by
  exact ⟨Frame.puts (F:=P) (a:=q) (hf:=hP.hue) (B:=B),
    Frame.fruit (F:=P) (a:=q) (hf:=hP.hue) (hX:=hP.toll) (h:=hσ) he hB hc⟩

end YM.Integration.FundedRankTwoPackets
