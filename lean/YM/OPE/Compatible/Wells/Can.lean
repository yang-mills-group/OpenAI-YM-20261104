import YM.OPE.Compatible.Wells.Rare
/-!
# Marginal plans. True relative density jets, *before* normalization
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.OPE.Owl.HillZ
open Function Filter MeasureTheory Lattice Laurent Wilson Matrix RG Gauge Precision
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ENNReal ContDiff
open Eyrie Push Push.AbsoluteSums Push.Mark Cascade Flume Flume.Page Flume.Script Pilot Finset
open Silt Libra Coin Rill Silt.Float Votive PertExtension Series GaussianScore Radial Next.Foundations
open Merchant Merchant.Aloof Merchant.Sleeve Merchant.SiteL
open Next.Free Next.Scheduling Stroke Spells Lass Lass.Zest Pill CardinalQ
variable {I:Type}{φ:Filter I}{G:Gauge} {K:Sponsor G}{T:Seasons K}
variable {β:I→ℝ}{n:I→Side}{S:Stage}{i j d r k:ℕ}{τ s a B:ℝ}
variable (A:∀ x:I,HillZ (T:=T) S i r d τ (β x) (n x))(U: Scaffold φ (Counters β) n (Mnd i S A) r)
variable (D:I→ Law (Merchant.Chamber G r))(hs:G.Simple)
open Merchant.SiteL
variable (h:Tendsto β φ atTop)(hD: GaugeD A U D)
open Cinders Metric Set Zeph Jargon Crown PertExtension Flock Stranded
variable {N:ChartRatio G} {s c R:ℝ} (H:StackP N s c R)(hN:LocalRatio N)
variable (x:∀ i,Bid.Dir G (n i)) (g:ℂ→L[ℝ]ℝ) (P:Pad G)
open ScriptJ
local notation "TC"=> Merchant.Chamber G r
local notation "X!"=>cEye A U D x
open Variance
local notation "m!"=> (ΓWeight (G:=G) (Punched A U _) (cEye A U D x _) (KPole A _) (LPole A _))
include hN
include hD
-- procurement point includes h∀ X ANY SEQUENCE
structure Loaded (f:Forge G n):Prop where
       fees :∀ᶠ i in φ,∀ x:∀ i,Bid.Dir G (n i), (f i).B ∧ draw (Tact A U D x N i *((f i)∘liftedM A U D x i)) (D i) (Chart.tangent G (fieldP r))=0 -- implicit N
omit hN hD in lemma moveB {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] (D:Law E)(μ:Measure E)[μ.IsAddHaarMeasure](W:ScriptJ E)(h:W.B)(p:ScriptJ E)(hp:p.B)(Z:Token)(hf:draw (W*p) D μ=0): draw (W*((fun _:E=>Z)*p)) D μ=0:=by
       rw[mul_left_comm,show draw ((fun _=>Z)*(W*p)) D μ=Z*draw (W*p) D μ from drips μ D (W*p) Z (height h hp),hf,mul_zero]
variable (e:↥(fieldP r))
omit hN in lemma pulseΦ (j:I): let Q:=KPole A j; let X:=cEye A U D x j; ∀ y:Merchant.Chamber G r,jet Q 2 (turn (Stair A U j) X y)=(D j).P y y/2+jet Q 2 X:=by
  dsimp only
  intro y
  have rearrange (p q c : ℝ) (h : -p - -q = -c / 2) : p = c / 2 + q := by
    linarith
  apply rearrange
  simpa only [PolV, liftedM, Yfar, turn] using sourZ A U D hD x j y
lemma entryS (j:I)(a:Bid.Dir G (n j)→ G.Color)(l:ℕ):
        let C:= Cake (sett (n j) 0 e.val) false (KPole A j) (LPole A j) a l; draw (Tact A U D x N j*(C∘ turn (sailT G (Punched A U j)) (cEye A U D x j))) (D j) (Chart.tangent G (fieldP r))=0:=by
            let μ:=Chart.tangent G (fieldP r)
            intro C; obtain ⟨z,h⟩:= ΓPhase A U D hN x j; let f':= KPole A j; let g':= LPole A j; let L:=D j; let Q:=Punched A U j; let x':=cEye A U D x j; let R:=turn (Stair A U j) x'; let v:= jet f' 2 x'; let W:=ΓWeight Q x' f' g' N z; have he:= pulseΦ A U D hD x j
            have hv: draw (W*(C∘ (turn (sailT G Q) x'))) L μ=0:=by with_reducible_and_instances exact ΓCake (k:=l) Q hN L x' e f' g' μ v he z a
            refine Eq.trans ?_ hv; with_reducible_and_instances exact congr_arg (fun (W:ScriptJ TC)=>draw (W*(C∘ (turn (sailT G Q) x'))) L μ) h
omit hN hD in
private lemma phase_paid {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
    (D : Law E) (μ : Measure E) [μ.IsAddHaarMeasure] (W : ScriptJ E) (hW : W.B)
    (R : E →L[ℝ] F) (u : F) (C : ScriptJ F) (hC : C.B) (z : Token)
    (hz : draw (W * (C ∘ turn R u)) D μ = 0) :
    ScriptJ.B ((fun _ : F => z) * C) ∧ draw (W * (((fun _ : F => z) * C) ∘ turn R u)) D μ = 0 := by
  exact ⟨height (Bfray z) hC, moveB D μ W hW (C ∘ turn R u) (turnB R u C hC) z hz⟩

omit hN hD in
private lemma phase_value {f : CrysP n G} (l : ℕ) (s : Libra.Char.Phase) (j : I) :
    LiftA s (Flan e.val (HabitK n (VesselP i S A)) (HabitL n (VesselP i S A)) f l) j =
      (fun _ : Bid.Dir G (n j) => (Libra.Shell.Ū : Token)^s.val) *
        Cake (sett (n j) 0 e.val) false (KPole A j) (LPole A j) (f j) l := rfl

omit hN hD in
private lemma actual_turn (j : I) : liftedM A U D x j = turn (Stair A U j) (cEye A U D x j) := rfl

lemma idCarga {f:CrysP n G}(l:ℕ)(s:Libra.Char.Phase)(j:I):
      let F:= LiftA s (Flan e.val (HabitK n (VesselP i S A)) (HabitL n (VesselP i S A)) f l)
      ScriptJ.B (F j) ∧ draw (Tact A U D x N j*((F j)∘liftedM A U D x j)) (D j) (Chart.tangent G (fieldP r))=0:=by
  have hz := entryS A U D hD hN x e j (f j) l
  dsimp only at hz
  dsimp only
  rw [phase_value A e l s j, actual_turn A U D x j]
  with_reducible_and_instances
    exact phase_paid (D j) (Chart.tangent G (fieldP r))
      (Tact A U D x N j) (Kgrade A U D hN x j) (Stair A U j) (cEye A U D x j)
      (Cake (sett (n j) 0 e.val) false (KPole A j) (LPole A j) (f j) l)
      (CakeB _ _ _ _ (f j) l) ((Libra.Shell.Ū : Token)^s.val)
      hz
lemma subLoad (f:CrysP n G)(l:ℕ)(e:↥(fieldP r))(s:Libra.Char.Phase): Loaded A U D (N:=N) (LiftA s (Flan e.val (HabitK n (VesselP i S A)) (HabitL n (VesselP i S A)) f l)):=by
            constructor; filter_upwards with j x; exact idCarga A U D hD hN x e l s j

lemma load {p q:Forge G n}(hv:WageK U.top (VesselP i S A) (ShadowP i S A U) (ShadowL i S A U) p q): Loaded A U D p (N:=N):=by
       let μ:=Chart.tangent G (fieldP r)
       induction hv with
       | empty=>
           constructor; filter_upwards with j x; constructor; exact Bfray (E:=Bid.Dir G (n j)) (0:Token); change draw (_*(0:ScriptJ TC)) _ μ=0; rw[mul_zero]; exact JetS.eta _ _ (Flock.singleConst ..) (Flock.singleConst ..) (Flock.singleConst ..)
       | add h h' ih ih' =>
           constructor; filter_upwards [ih.fees,ih'.fees] with j a b x; specialize a x; specialize b x; with_reducible_and_instances exact Lplus (D j) μ (Tact A U D x N j) (Kgrade A U D hN x j) (Stair A U j) (cEye A U D x j) a b -- λ X! maybe x scope
       | cong _ h ih=> constructor; filter_upwards[ih.fees,h] with j hx hy; rw [←hy.1]; exact hx
       | piece f l e s _=> exact subLoad A U D hD hN f l e s
where Lplus {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F][MeasurableSpace E][BorelSpace E] (D:Law E)(μ:Measure E)[μ.IsAddHaarMeasure](W:ScriptJ E)(h:W.B)(R:E→L[ℝ] F)(x:F){f g:ScriptJ F}(hf:f.B ∧ draw (W*(f∘turn R x)) D μ=0)(hp:g.B∧ draw (W*(g∘turn R x)) D μ=0): ScriptJ.B (f+g) ∧ draw (W*((f+g)∘turn R x)) D μ=0:=by
       refine ⟨ScriptJ.key hf.1 hp.1,?_⟩; rw[show (f+g)∘turn R x=f∘turn R x+g∘turn R x from rfl,mul_add, duoS μ D _ _ (height h (turnB R x f hf.1)) (height h (turnB R x g hp.1)),hf.2,hp.2,zero_add]
end YM.OPE.Owl.HillZ
