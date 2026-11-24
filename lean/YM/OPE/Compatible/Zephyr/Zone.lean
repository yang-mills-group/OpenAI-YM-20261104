import YM.OPE.Compatible.Zephyr.Fir
/-! # Operational exchange w ages -/
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
namespace Chase
variable (h:Chase A l)
variable {n:ℕ}(d:ι→ℕ)(hg:Lite A l (fun i=>(d i:ℝ)))(x:∀ i, Site (A i).c)(I:∀ i,Seats (A i).forest)(p:∀ i,Homer (A i) (x i) (d i) n (I i))
include h hg p
lemma shelterR :∃ v:ι→ℝ,Wage A l v (-(11/10))∧∀ᶠ i in l,
      Envelope (RockV (A i).R (barM A i) (I i))∧∀ U,‖RockV (A i).R (barM A i) (I i) U‖ ≤ v i:=by
       let X(i):=(p i).X; let τ:=E.ε/2; have ht:0<τ:=half_pos E.usable; have hs:0 ≤ sheen E:=by unfold sheen; linarith [E.grants.1,E.usable]
       have hX:= (h.dart d hg x I p).1
       let v i:=marksV (A i).R (p i).X P.top.width τ P.top.paths (loopBill G L (A i).x) (barM A i)+2*((p i).X.card*(est (A i).R.p τ*incomingE G L (A i).x)); let y i:= 2*(((p i).X.card:ℝ)*(est (A i).R.p τ*incomingE G L (A i).x)); have hv:= h.attraction (fun i=>(p i).X) hX τ; obtain ⟨hf,-⟩:= h.rosy d hg x I p _ (RateLE.const 0 h.tense)
       refine ⟨fun i=>v i+y i, hv.add (by simpa only [zero_add] using! ((RateLE.const (2:ℝ) h.tense).mul ((hX.sound h).mul ((h.winds τ).mul (h.run (incomingE_rate G L)))))) h.tense,?_⟩
       filter_upwards [hf,h.port] with i hi he; have hZ:= (hi.1).present (add_nonneg hs ht.le); have hP:sheen E + τ ≤ (A i).R.p.supportExponent:=by rw [he.budget.2.2.2.1]; unfold sheen τ;linarith [E.usable]
       have hk:= (childhood (crust (p i).good) he.budget.1 ht hP).present hs
       refine ⟨?_,fun U=> (norm_sub_le ..).trans (add_le_add (hZ.2 _) (hk.2 _))⟩
       have h':RockV (A i).R (barM A i) (I i)= cinnamon (A i).R (barM A i) (I i)+ (-tweak (I i) ((A i).R.activities.additive (A i).R.p)):=rfl
       rw [h']; exact hZ.1.add hk.1.neg -- sub_eq_add_neg not rfl?
lemma frozen (b:ι→ℝ)(hb: Wage A l b 0)(K:∀ i,(A i).V.Choices)(r t:ℕ)(hr:r≤t):
   let β i:= spillMass (G:=G) L t (A i).x
   let a i:= spillMass (G:=G) L r (A i).x
   ∃ f:ι→ℝ,Wage A l f (-(11/10))∧∀ᶠ i in l,∀ U:World (A i).forest (p i).H G,dazed (p i).good.nested (a i) (β i) U→
       Envelope (Arbor (A i).sheet.V (A i).R (K i) (I i) (p i).H (β i) U) ∧ ∀ g:World (A i).forest (I i) G→ℝ,Envelope g→ (∀ j, ‖g j‖≤ b i)→ ‖report (I i) (p i).H (A i).R (A i).sheet.V (barM A i) (K i) (β i) g U - Rails (A i).R (A i).sheet.V (K i) (I i) (p i).H (β i) U g‖ ≤ f i:=by
       intro B a; obtain ⟨v,hv,hP⟩:= h.shelterR d hg x I p; refine ⟨fun i=>4*(2*v i)*b i,by simpa only [zero_add,add_zero] using ((RateLE.const (4:ℝ) h.tense).mul ((RateLE.const (2:ℝ) h.tense).mul hv)).mul hb,?_⟩
       filter_upwards [h.high.eventually_gt_atTop 0,h.port,hP,h.tins t,h.dress,(((RateLE.const 2 h.tense).mul hv).tends (by norm_num) h.tense).eventually (ge_mem_nhds (show (0:ℝ)< 1/2 by norm_num))] with i hi hk hj hm hT hv U hu
       have hV :0≤ skimX G L (A i).x:= Real.rpow_nonneg (le_of_lt (by convert! hi)) _; have h'e : 1 ≤ echoL G L (A i).x:=Delay.bill_ge ..; have he':= furthers (A i).R (A i).sheet.V U (p i).good.nested (K i) (show a i≤B i from mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h'e hr) hV) (mul_nonneg hV (pow_nonneg (le_trans zero_le_one h'e) _)) hm hu (crust (p i).good) le_rfl hk.budget.1 hk.width hT.1 hk.port.1 hj.1 hj.2 hv
       exact ⟨he'.1,fun g=>he'.2 g _⟩
end Chase
end YM.PhysicalNext.Repeat.Aroma
