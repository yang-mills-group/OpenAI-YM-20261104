import YM.Qlocal.Feud.Drifts
/- # Shrinking both income & emitted letters using bought widths only. Preserve forecast unmasked rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Feud
open Function Filter Set Metric Lattice MeasureTheory ProbabilityTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid
open AllOrder Ker Laplace Laplace.SigmaP Response Catch
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open Marker Multi PertExtension.Series Radial Extra.Iteration Floe PositionX.Jet
open Comparison.RG02.Order
open Comparison.RG02.Assembly
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge} {k j i q r n:ℕ} {c f :Side}{S:StepData c f} {b α δ t:ℝ}
open Quipu.Sonnet
namespace Peak
open Quipu Quipu.Sonnet Tern
variable {ι σ:Type*}{V:Type}[DecidableEq V]{Z:Marker.Census V}
open Cider Quipu.Sonnet.Tern.Stanza Bind Horn
open PertExtension PertExtension.Series Sienna Lantern Catch Catch.Clock Aux.Name Presented Poll
variable {S':Catch.Clock ι}{P:Patch}{K:KernelChoices}{v:Stage}{u:ℝ→ℝ}{κ:ℕ}{F:Uniform.Before G v.width v.paths P.J K (k+3+3)}
variable (W:ι→ Aux.Name G P K u κ v (k+3) F)(g:V→ℕ)
variable (m o:ℕ)(A:ι→Stanza Z G g m) (p:∀ i,((A i).son o).Decision)
variable (C:ι→ℝ) (hA:∀ i,((A i).son o).Allows (α+b) (C i)) (ha:0<α) (hb:0 ≤ b) (hC:S'.Meter C 0)
    (x:∀ i:ι,V→Site (W i).f)(s:Senses Z) (n':ι→ℕ)
set_option quotPrecheck false
local notation "u'"=> rustic W g m o A p x s
local notation "X[" i "]"=> Stanza.son (A i) o
noncomputable abbrev lost : ∀ i, Tale.Decision (X[i]) := fun i => (X[i]).long (p i) (n' i)
noncomputable abbrev husk : ∀ i, Tale.Decision (X[i]) := fun i => (X[i]).short (p i) (n' i)
local notation "L"=> lost g m o A p n'
local notation "U"=> husk g m o A p n'
local notation "q₀"=> Quipu.Lagger.dues g s.val
local notation "R₀"=>fun i:ι=> Cider.nod b (n' i)
local notation "d"=> rustic W g m o A L x s
local notation "Q₀"=> rustic W g m o A U x s
variable (ht:Aux.Name.Proper W S')
include hA ha hb hC ht
lemma stills : Lane W u' S' j (q₀):= by
 have hs : ∀ (i:ι) (h:Fin (m+1))(j:Fin (h.val+Lagger.dues g s.val+1))(r:ℕ),p i s h j r→0≤((X[i]).array s h j r).momentum:= fun _ _ _ _ _=>Nat.zero_le _; let A':= slideScale (j:=j) W g m o A p C hA ha hb hC x s (fun _=>0) hs (fun _=>1) (?_) ht; swap; · exact Meter.const S' (|1| *Cider.nod b 0)
 simp_rw [one_smul] at A'; exact A'
lemma shutters : Shrunk S' j (q₀) R₀ (u') Q₀:= by
 let Δ(i):= -(Cider.nod b (n' i))⁻¹; let V(i):= Δ i • d i; have h: S'.Meter (fun i=> |Δ i| *R₀ i) 0:= Meter.eq_mem (Meter.const S' 1) (Eventually.of_forall fun i=>by dsimp only [Δ,Cider.nod]; rw [abs_neg,abs_of_pos (inv_pos.mpr (Real.exp_pos _)),inv_mul_cancel₀ (Real.exp_pos _).ne'])
 have he: Lane W V S' j (q₀):= slideScale W g m o A L C hA ha hb hC x s n' (fun i j q k hx=> (Nat.le_of_lt hx.2)) Δ h ht
 refine ⟨stills W g m o A p C hA ha hb hC x s ht,V,he, funext (fun i=>?_ )⟩; change Tale.markℓ _ _ _ _=_; rw [splitCost (X[i]) (p i) s (x i) (hA i) (add_pos_of_pos_of_nonneg ha hb)]; unfold V Δ; rw [smul_smul,mul_neg]; dsimp only [Cider.nod]; rw [mul_inv_cancel₀ (Real.exp_pos _).ne', neg_one_smul,sub_eq_add_neg]
-- MAY require supports of y-core through all Wealth.Form.Q.Weight.Owner. Estimate all.L.Frame.
variable (y:∀ i:ι,V→Site (W i).c)
noncomputable abbrev scene : ∀ i,Bind.reed G (W i).c:= fun i=> (X[i]).markℓ (p i) (y i) s
local notation "S"=> S'.rail
set_option quotPrecheck false
local notation "f0"=> scene W g m o A p s y
local notation "Q[" i "]"=> ℝ×(W i).X
-- mark tilt direction.Temp.C
noncomputable def horizon {c:Side} (R: Bind.reed G c): ℝ×Apex c G→ℝ:= fun z=> R z.1 (Campus.oracle G c z)
abbrev Ready (W:ι→ Aux.Name G P K u κ v (k+3) F) (S':Catch.Clock ι) (j:ℕ) (R:∀ i,Bind.reed G (W i).c): Prop:= ∀ p>(0:ℝ),∀ᶠ i in S'.rail, ∀ x:ℝ×(W i).X,‖x‖<1→ Brush j (S'.cost i^p) 1 (horizon (R i)) x
variable (hn:∀ i (h:Fin (m+1)) (j:Fin (h.val+Quipu.Lagger.dues g s.val+1)) k,p i s h j k→ n' i≤ (((A i).son o).array s h j k).momentum)
omit ht
include hA hn
lemma emit (P:ι→ℝ)(hp:S'.Meter (fun i=> |P i| * R₀ i) 0) : Ready W S' j (fun i=> P i • (f0 i)):=by
 obtain ⟨d0,hd⟩:= paint_supply G j; let v:=Cider.allowance G j o m (Lagger.dues g s.val) α (Campus.outerV G j d0); let V₁ i:= v*((|P i| * nod b (n' i))*C i); let R₁:=S'; have hh:S'.Meter V₁ 0:= ((hp.mul hC).lscale v).weak (by simp);
 intro r hr; filter_upwards [hh r hr] with i hi z hz; have hs:= Campus.whole hd z hz.le; let H:=((Cider.life s ((A i).son o) (p i) (hA i) (hn i) ha hb (y i) _ hs.1 Prod.fst hs.2 (allows_linear («L»:=ContinuousLinearMap.fst ℝ ℝ ((W i).X)) (ContinuousLinearMap.norm_fst_le ..) ((norm_fst_le z).trans hz.le))).smul (P i)); refine Brush.offer.mpr ⟨H.analytic.of_le le_top,fun j hj=> ?_⟩; refine (H.norm_le _ hj).trans ?_; change |P i| * (v*(R₀ i*C i)) ≤ _; rw [mul_left_comm,←mul_assoc (|P i|)]; exact (le_abs_self (V₁ i)).trans hi
omit hn

lemma fastened : Ready W S' j f0 := by
 have hs : ∀ (i:ι) (h:Fin (m+1))(j:Fin (h.val+Lagger.dues g s.val+1))(r:ℕ),p i s h j r→0≤((X[i]).array s h j r).momentum:= fun _ _ _ _ _=>Nat.zero_le _; let A':= emit (j:=j) W g m o A p C hA ha hb hC s (fun _=>0) y hs (fun _=>1) (by exact Meter.const S' (|1| * Cider.nod b 0)) ; simp_rw [one_smul] at A'; exact A'
def Razor (S':Catch.Clock ι)(W:ι→ Aux.Name G P K u κ v (k+3) F)(p:ι→ℝ)(j:ℕ)(R R':∀ i,Bind.reed G (W i).c) : Prop:= ∃ (wY: ∀ i,Bind.reed G (W i).c), Ready W S' j wY ∧ R' = fun i=> R i+p i • wY i
lemma sharp : Razor S' W (R₀) j f0 (scene W g m o A U s y):= by
 let δ(i):= -(Cider.nod b (n' i))⁻¹; let V(i):= δ i • scene W g m o A L s y i; have h: S'.Meter (fun i=> |δ i| *R₀ i) 0:= Meter.eq_mem (Meter.const S' 1) (Eventually.of_forall fun i=>by dsimp only [δ,Cider.nod]; rw [abs_neg,abs_of_pos (inv_pos.mpr (Real.exp_pos _)),inv_mul_cancel₀ (Real.exp_pos _).ne'])
 have he: Ready W S' j V:= emit W g m o A L C hA ha hb hC s n' y (fun i j q k hx=> (Nat.le_of_lt hx.2)) δ h
 refine ⟨V,he,funext fun i=>?_⟩; change Tale.markℓ _ _ _ _=_; rw [splitCost (X[i]) (p i) s (y i) (hA i) (add_pos_of_pos_of_nonneg ha hb)]; unfold V δ; rw [smul_smul,mul_neg]; dsimp only [Cider.nod]; rw [mul_inv_cancel₀ (Real.exp_pos _).ne', neg_one_smul,sub_eq_add_neg]
end Peak
end YM.Qlocal.Feud
