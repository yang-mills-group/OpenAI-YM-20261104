import YM.OPE.Compatible.Karu.Rev
/-!
# H.Launch supplies.Born.Cumul integrations at Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.PriceZ
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {v v' b:ℝ} {A:Alps K T i v}{D:Alps K T j v'}{U:Boxes G P K.K}
section
variable {W:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {s:W→ℝ}(Y Z:F→L[ℝ] F)(f g:W→ E→L[ℝ] F) {ν:W→Side}
variable (h:NPay ν f 0 1)(hh:NPay ν g 0 1)(he:NPay ν (f-g) 0 s)(p q:W→Dice F)(hp:NPay ν p k 1)(ht:NPay ν (p-q) i s)
include he h hh
lemma peachP:
    let a(j):=Y ∘L f j; let b(j):= Y ∘L g j
    NPay ν a 0 1 ∧ NPay ν b 0 1 ∧ NPay ν (a-b) 0 s:=by
       intro a b; refine ⟨?_,?_,?_⟩
       · simpa only [one_mul,Nat.add_zero] using! (FarCap (z:=a) (constantV (k:=0) ν Y) h zero_le_one (fun i=> ContinuousLinearMap.opNorm_comp_le Y (f i)))
       · simpa only [one_mul,Nat.add_zero] using! (FarCap (z:=b) (constantV (k:=0) ν Y) hh zero_le_one (fun i=> ContinuousLinearMap.opNorm_comp_le Y (g i)))
       simpa only [one_mul,Nat.add_zero] using! (FarCap (z:=a-b) (constantV (k:=0) ν Y) he zero_le_one (fun i=>show ‖a i-b i‖≤‖Y‖*‖f i-g i‖ from by rw [show a i-b i=Y ∘L (f i-g i) from ContinuousLinearMap.ext (fun x=> (map_sub Y (f i x) (g i x)).symm)]; exact ContinuousLinearMap.opNorm_comp_le ..))
include hp ht
lemma waxV (hs:0 ≤ s) :
   let D(j):= Y ∘L f j; let R(j):= Z ∘L f j; let D'(j):=Y ∘L g j; let R'(j):= Z ∘L g j
   let P(j):=rollD (D j) (R j) (p j); let Q(j):=rollD (D' j) (R' j) (q j)
   NPay ν P k 1∧ NPay ν (P-Q) (max k i) s:=by
      intro D R D' R' P Q
      obtain ⟨hD,hD',hD''⟩:= peachP Y f g h hh he; obtain ⟨hR,hR',hR''⟩:=peachP Z f g h hh he
      refine ⟨?_,?_⟩
      · simpa only [one_mul,Nat.add_zero] using! (flyP (a:=D) hD hR zero_le_one zero_le_one hp)
      let X(i):=rollD (D i-D' i) (R i) (p i); let U(i):=rollD (D' i) (R i-R' i) (p i); let V(i):=rollD (D' i) (R' i) (p i-q i)
      rw [show P-Q=X+U+V from funext fun i=>by change P i-Q i=(X i+U i)+rollD (D' i) (R' i) (p i-q i); rw [drag,show X i+U i=P i-rollD (D' i) (R' i) (p i) from (scorp (D i) (R i) (D' i) (R' i) (p i)).symm]; unfold Q; abel]
      have hy:NPay ν X k s:=by simpa only [one_mul,Nat.add_zero,mul_one] using! (flyP (a:=D-D') hD'' hR zero_le_one hs hp)
      have ha:NPay ν U k s:=by simpa only [one_mul,Nat.add_zero] using! flyP hD' hR'' zero_le_one zero_le_one hp
      have hv:NPay ν V i s:=by simpa only [mul_one,Nat.add_zero] using! flyP hD' hR' hs zero_le_one ht
      exact Lpay (p:=X+U) (t:=V) (costGauge ν
        (Lpay hy ha) hs le_rfl (le_max_left ..)) (costGauge ν hv hs le_rfl (le_max_right ..))
end
end YM.OPE.Quit.PriceZ
