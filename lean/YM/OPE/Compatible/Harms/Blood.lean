import YM.OPE.Compatible.Harms.Cane
/-!
# Activation along chase
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard AnalyticBridge.VerifiedReset Geo
open Next.Rank.Thirst YM.OPE
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P:Teller G} {D:Patch} {E:ConnectedActivityE6.Target G P} {L:Side} {W a σ C κ v γ t s w:ℝ} {m:ℕ}
variable {o:ConnectedActivityE6.Target.Order G W}
variable {ι:Type*} {l:Filter ι} {A:ι→ Model D P L E o κ C m}
open Push.Local Source
variable (x:ι→ℝ) {b k:ℕ}{Fr:Labels.Frame G k}(V:SectionData Fr)(O:Hol G) (p:ℂ→L[ℝ] ℝ)
section Physical
variable (M:∀ i,Coefficient Fr (A i).f) (F:∀ i,Config G (A i).f→ℂ)(Q:∀ i,Support (A i).f)(J:∀ i,Seats (A i).forest)
namespace Chase
variable (H:Chase A l)
variable {r s a b t:ι→ℝ} {α:ℝ}
variable {m':ℕ} (hg:∀ᶠ i in l, ‖(A i).g‖ ≤ spillMass (G:=G) L m' (A i).x)
local notation "S!"=> A
include H hg
lemma blood (hz:∀ᶠ i in l, 0 ≤ b i ∧ ((A i).R.p.Regular (Q i) (F i))∧ ((A i).R.p.supBounds 0 (Q i) (F i) (a i)) ∧ (M i).Format 0 O (A i).R ∧ (M i).remBound 0 (A i).R (s i) (t i) ∧ pledgesF (Q i) (J i) ∧(∀ U, ‖(M i).exponentialEntry 0 V (A i).R U‖ ≤ r i) ∧ ∀ U:Config G (A i).f,Healthy (A i).R.p.threshold (Q i) U→ ‖(M i).exponentialEntry 0 V (A i).R U-F i U‖≤ b i)
     (hy: Wage A l b α)(hk: Wage A l r 0)(hy': Wage A l a 0)(hr: Wage A l s α)(hf: Wage A l t 0)(hJ: Lite A l (fun i=>((J i).card:ℝ))) :
      Wage A l (fun i=>let T:=A i; let R:=T.R; let S:=T.V; p (S.push R.beta ((M i).density 0 V R) T.sheet.V)/ (S.push R.beta R.eval T.sheet.V)-T.arg (J i) (powerA (J i) R.p (Q i) p (F i))) α :=by
     obtain ⟨n,ht⟩:= H.terrainM _ hg
     let w(i):= ‖p‖*(r i+a i); let v(i):=(‖p‖*b i) + w i*((J i).card * Real.exp (-(echoM A i)^(2:ℕ)))
     let h(i):=(‖freight E L κ (A i).x‖ * ‖p‖)*(s i*t i); have hv : Wage A l v α:=by simpa only [v,w,Wage,zero_add] using (((RateLE.const ‖p‖ H.tense).mul hy).mono (le_of_eq (zero_add _))).add (((RateLE.const ‖p‖ H.tense).mul (hk.add hy' H.tense)|>.mono (le_of_eq (zero_add _))).mul ((hJ.sound H).mul (H.woe α))|>.mono (le_of_eq (by ring))) H.tense
     have hh: Wage A l h α := by simpa only [add_zero,zero_add] using ( (H.run (riseD E L H.2.2.2.1).1|>.norm).mul (RateLE.const ‖p‖ H.tense)|>.mul (hr.mul hf))
     apply RateLE.of_norm_le (hh.add hv H.tense)
     filter_upwards [ht,hz,H.tins n,H.port,H.high.eventually_gt_atTop 0] with i hT hB hΓ hP hU
     obtain ⟨hb,hF,he,hW,hζ,hI,hΨ,hQ⟩:=hB; have hx:= hP.budget.1; let R:=(A i).R; let S:=(A i).V; let I:= J i; let X:=(A i).sheet.V; let Z:=S.push R.beta R.eval X; have hp:0 < Z:= hT.branch
     let f:= cashX R.p (Q i) p (F i); let g:= ζPiece p R (M i) V 0
     have hw:0 ≤ w i:= mul_nonneg (norm_nonneg _) (add_nonneg ((norm_nonneg _).trans (hΨ 1)) he.1)
     have hi :f=powerA I R.p (Q i) p (F i) ∘ chant (A i).forest I:=funext fun j=>crownX p hF _ hI; have hX:Envelope f:=by rw[hi];exact Env.along (wrapX p (a i) hF he) (chant_m ..)
     have hy:= ζEnv p V hζ hW; have hu:S.patch.Branches S.kernel G:= hP.port.1; let B:= spillMass (G:=G) L n (A i).x; let A':=(A i).forest; have hc : 0≤ B:=mul_nonneg (Real.rpow_nonneg hU.le _) (pow_nonneg (zero_le_one.trans (Delay.bill_ge ..)) _)
     have hy' :‖S.push R.beta (R.eval * g) X-S.push R.beta (R.eval * f) X‖≤ Z*v i:=by
          have hC:Envelope (g-f):=by rw [sub_eq_add_neg]; exact hy.add hX.neg
          have hs':S.push R.beta (R.eval*(g-f)) X=S.push R.beta (R.eval*g) X-S.push R.beta (R.eval*f) X:=by unfold StepData.push; rw [mul_sub]; simp_rw[Pi.sub_apply,smul_sub]; exact integral_sub (StepData.push_slice (S.isKernel hu _) _ _ (((R.envelope hx).mul hy).integrable _)) (StepData.push_slice (S.isKernel hu _) _ _ (((R.envelope hx).mul hX).integrable _))
          rw [← hs']; apply contrast hu hx X hP.mass hT.flare hC (mul_nonneg (norm_nonneg _) hb) hw
          intro U; by_cases h':Healthy R.p.threshold (Q i) U
          · apply le_trans _ (le_add_of_nonneg_right (mul_nonneg hw (lantern ..))); rw [Pi.sub_apply]; unfold f cashX; dsimp only [Function.comp_apply]; rw [masked_eq _ _ _ _ h']; rw [show g U=p _ from rfl,← p.map_sub]; exact (p.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hQ U h') (norm_nonneg _)) -- rw η
          exact (norm_sub_le ..).trans ((add_le_add ((p.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hΨ _) (norm_nonneg _))) (sightW p _ he U)).trans ((le_trans (le_of_eq (mul_add ..|>.symm)) (le_mul_of_one_le_right hw (filmC hc hΓ hI _ h'))).trans (le_add_of_nonneg_left (mul_nonneg (norm_nonneg _) hb))))
     have hf': sheen E ≤ R.p.supportExponent:=by rw [show R.p.supportExponent=_ from hP.budget.2.2.2.1]; unfold sheen; linarith [E.usable]
     let P:= ((M i).density 0 V R); let a':=p (S.push R.beta P X); let f':=S.push R.beta (R.eval*g) X; let Q':= S.push R.beta (R.eval*f) X; have hx':‖a'-f'‖ ≤h i* Z:=κGrowth p X V hζ hW (S.isKernel hu _) hx hT.charge hf' hp.le
     change ‖a'/Z-_‖≤_
     rw [show (A i).arg I (powerA I R.p (Q i) p (F i))= Q'/Z from by unfold Q'; rw[hi]; rfl,← sub_div, norm_div,Real.norm_of_nonneg hp.le,div_le_iff₀ hp]; change ‖a'-Q'‖ ≤ (h i+v i)*Z; rw [show a'-Q'=(a'-f')+(f'-Q') by ring]; exact (norm_add_le ..).trans ((add_le_add hx' hy').trans_eq (by ring))
end Chase
end Physical
end YM.PhysicalNext.Repeat.Aroma
