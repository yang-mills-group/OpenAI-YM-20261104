import YM.Contacts.Model.Recover
/-! Recover small-f price on the aggregate jets, despite lack of budget on simultaneous values at different periods. Symbols before flags. -/
noncomputable section
namespace YM.Contacts.Model
open Function Lattice Finset Filter Set PhysicalNext.Repeat Pressure Wilson MeasureTheory RG
open Slide (Stars)
open Trio (froth Mirrors Offer)
open AnalyticBridge VerifiedReset Push.AbsoluteSums Animals YM.Stationary Milling PertExtension.Series Exterior Precision Ion
open Pulse Spine Garf Steam Bloch Radial House Lumen Metric Push.Uniform Kale
open scoped Topology NNReal InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{n m c:Side}{k w r z ℓ i j:ℕ}
open Lintel.Plata ConnectedActivityE6
open Slope
-- all-field regular. Not all-field analytical.
variable {C Λ μ:ℝ} {X:G.ColorIndex}{P:Bed}(B:BudgetPoint)(F:bore G)(p:Clip)(R:PathData G)
  (hP:R.Bounds p μ C Λ)(he:Aegis X F P)(hi:i<k+3)
include hP he hi
def leafSmooth (f:Config G m→ℝ):= ∀ U:Config G m, ContDiffAt ℝ ∞ (f∘ increment U) 0
lemma anchor_m (m:Side) : Measurable (anchor p R F m (k+3) i):= by
   have hx : Measurable (base p R m i):= by
      let f (t : ℝ):=Lintel.Angle.material (f:=m) p R t; have hh t: Measurable (f t):= (material_integrable hP m).comp (f:=fun U:Config G m=> (t,U)) (measurable_const.prodMk measurable_id)
      unfold base; split; · refine (show mainTerm p R=f 0 from ?_) ▸ hh 0; exact funext fun u=>by simp [f,Lintel.Angle.material]
      split; · refine (show Precision.loop R=f 1-f 0 from ?_) ▸ (hh 1).sub (hh 0); exact funext fun u=>by simp [f,Lintel.Angle.material]
      exact measurable_const
   exact ((Kale.planted ((should he.blazing).protects k m i hi)).consent.measurable.sub hx)
omit he hi in
lemma anchor_smooth (m:Side) : leafSmooth (anchor p R F m (k+3) i):= by
   let v:=wind (hair F m) (k+3) i; let a:= Kale.fire v; let b:=Kale.mirror a; intro U; let V : Directions G m→ Config G m:=increment U
   have he j : ContDiffAt ℝ ω (fun x=> G.mat (V x j)) 0:= by simp only [V,increment,G.mat_mul]; exact ((G.exp_jet.comp (contDiff_apply ..)).mul contDiff_const).contDiffAt
   have hx (s : Signed): ContDiffAt ℝ ∞ (fun x=> a (pull s 0 (V x))) 0:= by
      let v' z:= pull s (0:Site m) (V z); let W z:= Kale.alive (v' z)
      have hy (x):ContDiffAt ℝ ω (fun z=> G.mat (v' z x)) 0:= by
         unfold v' Lattice.pull Lattice.Step.read; split; next _=> simp only [G.mat_inv]; exact (starL ℝ).contDiff.contDiffAt.comp _ (he _)
         exact he _
      have hv (x):ContDiffAt ℝ ω (fun z=> G.mat (bring (v' z) x)) 0:= by
         suffices h: ∀ (x:Site m) (w:Lattice.Walk), ContDiffAt ℝ ω (fun z=> G.mat (travel (v' z) x w)) 0 from h _ _ ; intro x w; induction w generalizing x with
         | nil=>exact contDiffAt_const
         | cons a w ih=> simp_rw [travel,G.mat_mul]; apply ContDiffAt.mul; swap; exact ih _
                         unfold Lattice.Step.read; split; next _=> simp only [G.mat_inv]; exact (starL ℝ).contDiff.contDiffAt.comp _ (hy _)
                         exact hy _
      have ha x : ContDiffAt ℝ ∞ (fun z=> G.mat (W z x)) 0:= by
         unfold W alive Lattice.gauge; simp only [G.mat_mul,G.mat_inv]; exact ((hv _|>.of_le le_top).mul (hy _|>.of_le le_top)).mul ((starL ℝ).contDiff.contDiffAt.comp _ ((hv _).of_le le_top))
      have ho : ContDiffAt ℝ ∞ (fun z=> bevel m (W z)) 0:= (arm G m 1).symm.contDiff.contDiffAt.comp 0 (contDiffAt_pi.mpr (fun i=> (guardChar G).smooth _ (ha _))) -- ambient
      exact (wind_ana _ _ _ _).contDiffAt (n:=∞) |>.comp _ ho -- polynomial smooth v; wind_ana all?
   have hc: ContDiffAt ℝ ω (base p R m i ∘ V) 0:= by unfold base; split; exact Work.F02.mainTerm_contDiffAt hP he; split; exact Progress.Joint.loop_born hP V he; exact contDiffAt_const
   exact ContDiffAt.sub (f:=b ∘ V) (contDiffAt_const.mul (ContDiffAt.sum (s:=univ) (f:=fun s z=>a (pull s 0 (V z))) (fun s _=> hx s))) (hc.of_le le_top)
lemma anchor_bill (m:Side) : B.Regular univ (anchor p R F m (k+3) i):= by
   have ht U: ContDiffAt ℝ ((B.order:ℕ∞):WithTop ℕ∞) (anchor p R F m (k+3) i ∘ increment U) 0 := (anchor_smooth F p R hP m U).of_le (WithTop.coe_le_coe.mpr le_top)
   refine ⟨?_,anchor_m F p R hP he hi m,?_ , fun u _=> ht u,fun _ _ _ _ hh=> Next.Foundations.left_has _ hh (ht _)⟩
   · intro U V h; exact congr_arg _ (funext fun i=> h i (mem_univ _) (mem_univ _))
   intro s U;  refine congr_arg₂ (·-·) ((Kale.planted ((should he.blazing).protects k m i hi)).invariance _ _) ?_; unfold base; split; exact Work.F05.mainTerm_gauge hP U s; split; exact Work.F05.loop_gauge hP U s; rfl

variable {D: Stars→ Side}(Q:∀ i:Stars,(D i).val=2*(ℓ+i.val))
omit hP he hi
variable {f:Story G}
def lend (f:Story G) (s:Signed) (i:Site m) := pass f m 0 ∘ (VerifiedReset.Seat.view (s,i)) -- oriented about local launch (i)
lemma ties (F:Story G)(u:Site m): pass (hue F) m u= VerifiedReset.factor • (∑ s:Signed, lend F s u):= by
   ext V; change hue F (expandAt u V)=_; unfold hue lend Seat.view pass; rw [Pi.smul_apply,Finset.sum_apply]; apply congr_arg; refine Finset.sum_congr rfl fun s _=>?_ ; dsimp only [Function.comp_apply]; rw [expandAt_pull]; simp only [affine,Signed.act_zero,zero_add]
lemma tilt_share (u:Site m)(s:Signed): Seat.spread (s,u) (neighbors z 0)=neighbors z u:= by
    rw [show Seat.spread (s,u) (neighbors z 0) = neighbors z (Lattice.affine s u 0) from (Turn.circle_wind s u 0 z).symm]; simp [Lattice.affine]
lemma lent (z:ℕ)(h:B.Regular (neighbors z (0:Site m)) (pass f m 0))(u:Site m): B.Regular (neighbors z u) (pass (hue f) m u):= by rw [ties]; exact CouplingShape.reg_scale _ (Meadow.regularA _ (fun j _=> (tilt_share u j (z:=z)) ▸ ((Seat.regular (f:=pass f m 0) (j,u) h : B.Regular (Seat.spread (j,u) _) (lend f j u)))))
variable {Y:∀ s:Stars,Config G (D s)→ℝ}
lemma regular_clock (hq:ℓ+4≤z)(ha:∀ s,B.Regular univ (Y s)) (u:Site m): B.Regular (neighbors z u) (pass (Model.clock Q Y) m u):= by
   rw [show pass _ m u=∑ i:Stars,Slide.ray i • (Y i ∘ Slide.shape (Trio.pad Q i) u) from funext fun V=> by rw [Finset.sum_apply]; rfl]; refine Meadow.regularA _ fun i _=> CouplingShape.reg_scale _ (Slide.regular (Trio.pad Q i) u (ha i) fun y=> ?_);
   apply (neighbors_mem ..).2; exact (Slide.village (w:=ℓ+i.val) (Q i).ge _ _).trans (by have ht:=i.isLt; omega)
include hP he hi
lemma oak (hc:ℓ+4≤z) (u:Site m): B.Regular (neighbors z u) (pass (energy p R F Q (k+3) i) m u):= lent B z (regular_clock B Q hc (fun _=> anchor_bill B F p R hP he hi _) 0) u
end YM.Contacts.Model
