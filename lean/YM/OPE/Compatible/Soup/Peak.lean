import YM.OPE.Compatible.Soup.Store
/-!
# Conditional integration of the chamber observable

`Gabe` evaluates `Glaco` at the scale parameter `et A j`. Given `Startup`,
`suprising` bounds the integral of `Gabe` over `ChartS` at each exponent above
`Deb`. Under the stated field and chamber-law estimates, `decipher` controls the
complement and gives a `Wax` bound at exponent `Deb` for the full integral under `ShoreP D`.
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
variable {A:∀ x:I,HillZ (T:=T) S i r d τ (β x) (n x)}{U: Scaffold φ (Counters β) n (Mnd i S A) r}
variable (D:I→ Law (Merchant.Chamber G r))(hs:G.Simple)
open Merchant.SiteL
variable (h:Tendsto β φ atTop)(hD: GaugeD A U D)
open Cinders Metric Set Zeph Jargon Crown PertExtension Flock
variable {N:ChartRatio G} {s c R:ℝ} (H:StackP N s c R)(hN:LocalRatio N)
variable (x:∀ i,Bid.Dir G (n i)) (g:ℂ→L[ℝ]ℝ) (P:Pad G)
variable {D} (hp:Lyd A φ x)
open ScriptJ
section
-- selector. Large on disrupted patches
variable {F:I→Type} [∀ i,Nonempty (F i)] {E:I→Type}[∀ i,Norm (E i)] {T:I→ℝ} {L:∀ i, Set (F i)} {p: (i:I)→ F i→ E i}
lemma Mappable (ht:Tendsto T φ atTop)(hs:s<a)(he:∀ᶠ i in φ,(L i).Nonempty)(h:∀ x:(i:I)→ F i,(∀ᶠ i in φ,x i∈ L i)→ RateLE φ T (fun i=> ‖p i (x i)‖) s): Large L φ T p a:=by
       let b(i:I):=Real.exp (a*T i); let X (i:I):=∃ j∈L i, ¬(‖p i j‖≤ ‖b i‖); let x(i:I):F i:= if ht:X i then ht.choose else if hg:(L i).Nonempty then hg.choose else Classical.arbitrary _
       have hx := he.mono (show ∀ i,(L i).Nonempty → x i∈L i from fun i h=>by unfold x; split; rename_i hi; exact hi.choose_spec.1; exact h.choose_spec); refine ⟨b,RateLE.exp _ ht, ((h x hx a hs).mono fun i hi j hj=> by
             by_contra hp; have h:X i:=⟨j,hj,hp⟩; change ‖‖p i (x i)‖‖ ≤ _ at hi; erw [show x i=h.choose from dif_pos h] at hi; exact h.choose_spec.2 ((le_trans (Real.le_norm_self _) hi).trans (Real.le_norm_self _)))⟩
end
variable (A U D)
section
open Flume.Virgin
include hN
private lemma BoY (j:I):Measurable (ConV A U D x g N j):=by
       let x'(p:Merchant.Chamber G r):= et A j • (p+Odds (r:=r) x j); let c:= Bo A U g x j
       have ht:Measurable c:= (show Continuous c from (g.continuous.comp ((A j).realm.comp (monoInst ..))).div_const _).measurable; have he: Continuous x':=(by unfold x'; fun_prop); have hr:Measurable (@feeX G ↥(fieldP r) _ N):=Finset.measurable_sum _ (fun i _=> (Real.measurable_log.comp hN.borel).comp (measurable_pi_apply ..)) 
       let p(v:Merchant.Chamber G r):= ((D j).P v v/2); have hh : Continuous p:=by
           let L:=D j; rw [show p=(fun i=> -Real.log (L.kern i)) from (funext ?_)]
           · exact (L.continuous_kern.log (fun _=> (Real.exp_pos _).ne')).neg
           intro i; unfold p Law.kern; rw[Real.log_exp]; unfold L; ring
       exact (ht.comp (putC.comp he|>.measurable)).mul (Real.continuous_exp.measurable.comp ((hr.comp he.measurable).add hh.measurable))
end
variable {A U D}
set_option quotPrecheck false
local notation "X_C!"=> liftedM A U D x
local notation "KJ"=> Glaco A U D N P x g
noncomputable abbrev Gabe (j:I)(y:Merchant.Chamber G r):ℝ:= (Glaco A U D N P x g j y).atK (et A j) 
include hp h hD H hN hs
lemma Gabe_grain : Grain (ShoreP D) φ (Counters β) (Gabe (N:=N) (A:=A) (U:=U) (D:=D) x g P) 0:= (props (greetK hs h hD H hN x g P hp) (carth h) ((poleV A h).mono (by norm_num))).2.1
lemma suprising (hy: Deb < a) (P':I→ℝ)(hX: Startup A U (cEye A U D x) P' s c D) : let V:= ChartS A (cEye A U D x) P' s; let j(i:I):=∫ y in V i, Gabe (U:=U) (N:=N) (A:=A) (D:=D) x g P i y ∂ShoreP D i; Wax β φ j a:=by
       let P0:=cEye A U D x; intro V j; let B:=Gabe (U:=U) (N:=N) (A:=A) (D:=D) x g P; let q:= ConV A U D P0 g N; let C:= ShoreP D; let L:=carth h; have hG:= Gabe_grain hs h hD H hN x g P hp; have hr: Large V φ (Counters β) (q-B) a:=by
             refine Mappable L hy (hX.zero.mono fun j hj=>⟨0,hj⟩) (fun z hv=>?_); exact (vitalQ hs h hD H hN x g P z hp (picks A U h H.sweep P0 P' (Lyn hs h hD x hp) hX z hv)).norm 
       have hv: Grain C φ (Counters β) (fun i=> (V i).indicator (fun y=> q i y-B i y)) a:=by
             have he:∀ᶠ i in φ,AEStronglyMeasurable ((V i).indicator ((q-B) i)) (C i):= hG.integral.1.mono fun i hi=> (((BoY A U D hN P0 g i).aestronglyMeasurable).sub hi.aestronglyMeasurable).indicator (ChartC A P0 P' i)
             exact Large.crop (Eventually.of_forall fun i=>ChartC _ _ _ _) hr he
       have hV: Wick β φ (fun i=>∫ y in V i,q i y ∂C i):= scaleΞ A U D hs h H.sweep hN P0 g P' hX hD; apply ((hV a).sub hv.integral.2 L).congr; filter_upwards [hG.integral.1,hv.integral.1] with i hi hj; rw [integral_indicator (ChartC A P0 P' i)]; have hs: IntegrableOn (q i-B i) (V i) (C i):=(integrable_indicator_iff (ChartC A P0 P' i)).1 hj; have he: IntegrableOn (q i) (V i) (C i):=(sub_add_cancel (q i) _) ▸ (hs.add hi.integrableOn); rw [integral_sub he hi.integrableOn]; exact sub_sub_cancel ..
-- Integrate the observable evaluated at the scale parameter over the full chamber law.
lemma decipher : Wax β φ (fun i=> ∫ y, Gabe (A:=A) (U:=U) (D:=D) (N:=N) x g P i y ∂ShoreP D i) Deb:=by
       obtain ⟨Q,hQ⟩:=staff A U hs h H.sweep (cEye A U D x) (Lyn hs h hD x hp) hD; let q:=cEye A U D x; let V:=ChartS A q Q s; let F:= Gabe (N:=N) (A:=A) (U:=U) (D:=D) x g P; let B(i):=∫ y,F i y ∂ShoreP D i; let z(i):=∫ y in V i,F i y ∂ ShoreP D i; intro a ha; obtain ⟨b,hb,Hb⟩:= exists_between ha; have hp':Wax β φ z b:=suprising hs h hD H hN x g P hp hb Q hQ; let hv:=missingI F V (Eventually.of_forall fun i=>ChartC A q Q i) hQ.rebate (carth h) (Gabe_grain hs h hD H hN x g P hp) b; refine (show Wax β φ B b from RateLE.congr (hp'.sub hv (carth h)) (Eventually.of_forall fun j=>sub_sub_cancel ..)) _ Hb
end YM.OPE.Owl.HillZ
