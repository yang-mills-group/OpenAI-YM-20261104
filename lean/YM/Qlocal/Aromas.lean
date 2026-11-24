import YM.Qlocal.Therm
import YM.AllOrder.Docket.Tier
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Bind
open Function Filter Set Metric Lattice MeasureTheory ProbabilityTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid
open AllOrder Ker Laplace Laplace.SigmaP Response Catch
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open Marker Multi PertExtension.Series Radial Extra.Iteration Floe PositionX.Jet
open Comparison.RG02.Order
open Comparison.RG02.Assembly
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge} {k j i q r:ℕ} {n c f :Side}{S:StepData c f} {b α t:ℝ}
open PertExtension PertExtension.Series Sienna Lantern Catch Catch.Clock tether
variable {ι:Type*}{S':Catch.Clock ι}{P:Patch}{T:KernelChoices}{v:Stage}{u:ℝ→ℝ}{κ:ℕ}{F:Uniform.Before G v.width v.paths P.J T (k+3+3)}
open Aux.Name Presented  Poll
local notation "I"=>Aux.Name G P T u κ v (k+3) F
variable (Q : Aux.Name G P T u κ v (k+3) F)(R: reed G Q.f) (b:ℝ)
set_option quotPrecheck false
local notation "H"=> changes Q.Fs Q.shape R b (Aux.scope κ)
local notation "w"=>Q.Θ
local notation "Zed"=>Q.Fs.Slice G
local notation "V"=> Desk.night (G:=G)
local notation "X"=>Q.X
local notation "N"=> Poll.Body Q.Vx
--unused
-- exact positive/negative Boost readout on auxiliary higher comparison
variable (O:ChartRatio G)(hO:LocalRatio O) (hR:Flute R q) {s:Age→ℝ} (h:Q.Civil s) {x0 y:Q.X} (D C:ℝ) (hQ: Q.goods O D C x0)(hx: ‖y‖ < eaves G P.L Q.whenP)(he: ‖y - x0‖≤ furl G P.L Q.whenP)
namespace Aurum
local notation "θ"=> boost Q.Fs Q.choices Q.shape (Aux.scope κ) Q.legal R b (Q.enters O hO) hR -- signature?
-- for each unmarked program.Arbitrary Bright.Work.Full.Binding.
abbrev meters (x':X): Word ℝ:= fun j=> ratePlan (θ) j x' - Q.intercept O j
abbrev billing (x':X)(z:N) := unroll (A:=Q.Ph) (B:=Q.Bank O) (M:=Q.Zc) (ρ:=Q.Mh) («V»:= H) (W:=x') z
include hR hO
lemma phase_lecture (x':X)(he:∀ i≤j,Integrable (fun y=> someJ (billing Q R b O x' y) i) (Poll.sweep (Q.Zc 0)⁻¹)): meters Q R b O hO hR x' j=
    (Q.clean O x' j)+ Laplace.SigmaP.logS (Catch.coin H x' (A:=Q.Ph) (B:=Q.Bank O) (M:=Q.Zc) (ρ:=Q.Mh)) j:= by
 let L:= θ; have hv: ContDiffAt ℝ ω (fun _ : ℝ=> x') 0:= contDiffAt_const; let K':= L.hard; let f':= primitive (f:=Q.f) Q.tube.up Q.tube.high
 have hx t: Envelope (risky Q.shape f' (Aux.scope κ) b R t):= by
    let H':= (orchestra (f:=Q.f) _ _ Q.shape (Aux.scope κ) Q.legal t Q.path.choose_spec|>.fit); exact H'.add (tether.first R hR b t).neg
 let t:= L.quiet ∘ course x'; let A':= 1-L.perk (course x') t; have hp:0<L.perk (course x') t +A':= by unfold A'; simp
 have h1:0<L.paid 0:=mul_pos (pow_pos hO.scale _) (Real.exp_pos _);
 have hE : logS (L.drawdown (course x') t)=Function.swap (ratePlan L) x':= Grant.income Q.loom.large.1 hx x' h1 hO -- normative.
 have hz:= receives (n:=j) _ _ (Q.soft O hO) (O.scale^Fintype.card Q.Fs.Free) A' hp (Bind.slope _ _ _ Q.legal R b hR) (pow_pos hO.scale _) he; unfold meters; rw [← show logS (L.drawdown (course x') t) j=ratePlan (θ) j x' from congr_fun hE j, show logS (L.drawdown _ _) j= Q.intercept O j+ Q.clean O x' j + logS (Catch.coin H x' (A:=Q.Ph) (B:=Q.Bank O) (M:=Q.Zc) (ρ:=Q.Mh)) j from hz]; abel -- alignment HAccent.G.
section growth
variable (W':ι → Aux.Name G P T u κ v (k+3) F) (V':∀ i, reed G (W' i).f) (H': Horn.Lane W' V' S' (k+3) q) (hW: Aux.Name.Proper W' S')
local notation "S₀"=> S'.Meter
local notation "V₀"=> changes
variable (a:ℝ)
variable {p:ι→ℝ}{x y:∀ i,(W' i).X}(ht : ∀ᶠ i in S'.rail, (W' i).goods O D (p i) (y i))(hv:S'.Meter p 0)(hp:(S').Meter (fun i=> ‖x i‖) (-(1/2))) (hy:∀ᶠ i in S'.rail,‖x i-y i‖ ≤ furl G P.L ((W' i).whenP))(hD:0<D)
omit hR
include hO ht hp hv hD H' hW
local notation "φ"=> fun i:ι=> feed (W' i) (V' i) a O D (x i)
local notation "ψ"=> fun i:ι=> (W' i).scaleO O (x i)
local notation "χ"=> fun i:ι=> now (W' i) (V' i) a (x i)
local notation "U"=> fun i:ι=> (W' i|>.Θ)
local notation "K"=> fun i:ι=> meters (W' i) (V' i) a O hO (H'.tells i) ((W' i).tulip (x i))
lemma promised : Tendsto φ (S').rail (𝓝 1) ∧
    TaylorCap S' k (U) (fun i=> Lantern.shade ((W' i).Zc) 0-(W' i).tenses O (x i)+Real.log (φ i)) (K):= by
 let A:=stand D hO W' hW hD (ht.mono fun i hi=>hi.1.1) hv
 let h' := Aux.Name.enorth W' hW hp; let S:=Horn.timing W' V' H' hW a; obtain ⟨hh,hR⟩:= early_line («V»:=fun i=> changes (W' i).forest (W' i).shape (V' i) a (Aux.scope κ)) A h' S; let t:= receiptA A h'; refine ⟨hh, ?_⟩
 apply TaylorCap.fit (t.pair hR); · filter_upwards with i; have hv:= (W' i).amend hO (x i); change (_:ℝ)+Real.log (φ i)=_; rw [hv]; rw [neg_add_eq_sub,sub_sub_self]
 let μ₀ (i):= Poll.sweep ((W' i).Zc 0)⁻¹; let Hμ t y:= billing (W' t) (V' t) a O ((W' t).tulip (x t)) y; -- H syntax
 intro j hj; filter_upwards [eventually_all.mpr (show ∀ t:Fin (j+1),∀ᶠ i in S'.rail, Integrable (fun z=> someJ (billing (W' i) (V' i) a O ((W' i).tulip (x i)) z) t.val) (μ₀ i) from fun z=> Catch.ahead A h' S (by have ht:=z.isLt; omega))] with i hi; exact Eq.symm (phase_lecture _ _ a _ hO (H'.tells i) _ (j:=j) (fun p hp=> hi ⟨p,by omega⟩))
-- Need rim bound using full `allReal`. ht governing not needed for tangential rind
include hy
omit hO ht hp hv hy hD in
lemma cheer : ∀ᶠ i in S'.rail,∀ X': Config G (W' i).f, flags (W' i).price.threshold X'=∅→ color (V' i) a (W' i).Θ X' ≤ 3:= by
 have hh := H'.allReal (1/4) (by norm_num); have h0 := Meter.mul ((Aux.Name.Proper.meter W' hW).1.ab.lscale |a|) (Meter.pale S' (1/4)); filter_upwards [hh,h0.low (by norm_num : -(1/2:ℝ)+1/4<0) zero_lt_one] with i hi hp'; intro X' hx; let t:= V' i (W' i).Θ X'; let r:= fig (V' i) a (W' i).Θ X'; change ramp r≤_; have hz:|r| < 1:= by
    change |a*(W' i).Θ*t| < 1; simp_rw [abs_mul]; apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hi X' hx) (mul_nonneg (abs_nonneg _) (abs_nonneg _))) ((le_abs_self _).trans_lt hp');
 unfold ramp; rw [abs_lt] at hz; nlinarith [hz.1,hz.2]
lemma shepherd (s:ℝ) : S₀ (φ- (χ)/(ψ)) s:= by
 let r:= min s (-1); let t (x:ι):= S'.cost x ^ r; have hr: r<0:= by exact (min_le_right ..).trans_lt (by norm_num)
 have he:= ((Meter.pale S' r).down hr); let p0 := φ; have h:= (promised O hO D W' V' H' hW a ht hv hp hD);-- filled below
 have hF:S₀ φ 0:= (Clock.Meter.const S' (2:ℝ)).smaller (by have ht : Tendsto (fun i=>|φ i|) S'.rail (𝓝 |(1:ℝ)|):= continuous_abs.continuousAt.tendsto.comp h.1; exact (ht.eventually (gt_mem_nhds (by norm_num : |(1:ℝ)| < |(2:ℝ)|))).mono fun _ h=>h.le)
 have hA(Y₀:ι→ℝ)(he:S₀ Y₀ r): S₀ (φ- fun i=> Real.exp (Y₀ i)*(φ i)) r:= by
    let p':ι→ℝ:=fun _=>0; have hy := Clock.Meter.close (T:=S') Real.exp Real.contDiff_exp.contDiffAt (a:=p') tendsto_const_nhds (he.down hr) (show S₀ (_ -Y₀) r from ((Meter.nil S' r).sub he)); exact ((hy.mul hF).weak (by simp)).eq_mem (Eventually.of_forall fun i=> (by simp [p']; ring))
 let u i:= Real.exp (-t i)* (φ i); let z i:=Real.exp (t i)* (φ i)+ (3*Real.exp 1)* Aux.Name.tired D (W' i);
 refine ((Aux.Name.squeezes (f:=φ) (u:=z) (v:=(χ)/(ψ)) (g:=u) (hA (fun i=> -t i) ((Meter.pale S' r).neg)) (((hA t (Meter.pale S' r)).sub ((Aux.Name.tired_cost D W' hW hD r).lscale (3*Real.exp 1)))|>.eq_mem ?_) (?_))).weak (min_le_left ..)
 · exact Eventually.of_forall fun i=>by unfold z; simp only [Pi.sub_apply, Function.comp_apply]; ring
 obtain ⟨s,hS,hL⟩:= hW.legible; filter_upwards [ht,hp.stricter (by norm_num [vow] : -(1/2:ℝ)<vow), hy, hL, hW.look.same, Aux.Name.Proper.bandwidth W' hW r hr, cheer W' V' H' hW a] with i hi hI hu hl hY hZ hE; have hb:‖x i‖ < eaves G P.L ((W' i).whenP):= (le_abs_self _).trans_lt (by rw [hY] at hI; exact hI); apply accounting (W' i) (V' i) a O hO (H'.tells i) hl D _ hi hb hu (t i); intro V' hv; exact ⟨(hZ V' hv).1,(hZ V' hv).2,hE V' hv⟩
-- step order Taylor Cap in Log. expo read later (relative). 
lemma patterned : (∀ᶠ i in S'.rail,0< now (W' i) (V' i) a (x i)) ∧ TaylorCap S' k U (fun i=> Real.log (χ i)-(W' i).basis O) K:= by
 obtain ⟨he,hV⟩:= promised O hO D W' V' H' hW a ht hv hp hD; let A:=graded (k+1); let f:= φ; let g(i:ι):=χ i / ψ i; have h':A<0:=(by unfold A graded; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) k]); have hp:S₀ (f-g) A:= shepherd O hO D W' V' H' hW a ht hv hp hy hD A
 have ht:= uniform he hp h'; have hs(i):0< ψ i:= mul_pos ((W' i).born O hO) (Real.exp_pos _); have hu :∀ᶠ i in S'.rail,0<χ i:= (ht.eventually (lt_mem_nhds zero_lt_one)).mono fun i hi=> by have hi:0<χ i/ψ i:=hi; exact (div_pos_iff_of_pos_right (hs i)).1 hi
 refine ⟨hu,hV.alteration ( (Clock.Meter.close (T:=S') Real.log (Real.contDiffAt_log.mpr one_ne_zero) he ht hp).neg.eq_mem (hu.mono fun i hi=> ?_))⟩; -- from Docket/Tier
 change -(Real.log (φ i)-Real.log (g i)) = (Real.log (χ i)-(Real.log ((W' i).overhead O)- Lantern.shade ((W' i).Zc) 0))- (_- _+ Real.log (φ i)); unfold g; rw [Real.log_div hi.ne' (hs i).ne']; unfold scaleO; rw [Real.log_mul ((W' i).born O hO|>.ne') (Real.exp_pos _).ne', Real.log_exp]; ring
end growth
end Aurum
end YM.Qlocal.Bind
