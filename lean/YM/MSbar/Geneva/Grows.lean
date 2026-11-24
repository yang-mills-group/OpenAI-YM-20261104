import YM.MSbar.Geneva.Sells
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Geneva
open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film
open Measuring Cane Laurent Bloch UVNext.PricedKernels Spruce Lapaz Mosaic Issue RawP JetTab Bristol
open Next.SectorChange Bulk Posture JetTab
variable {G:Gauge}{X f g:ℕ→ℝ}{A:ℕ→Issue G}(hX:Tendsto X atTop atTop) {p m k q:ℕ}
variable (χ:ChartRatio G)(J:Voice G)(H H':Stage)(P:Patch)(D:KernelChoices)
variable (h:G.Simple) (hD:P.Branches D G)(hQ: Clear G J)(hχ:LocalRatio χ)
variable (M:StageCost)(i':G.ColorIndex){b:ℝ} (hp:∀ᶠ i in atTop,Paid (A i) P H H' J (X i)) (hq:∀ᶠ i in atTop,(A i).S.kernel=D)
variable (hc:∀ᶠ i in atTop,Festival (A i) χ p i'∧ ClockD (A i) p m M.s (X i)∧ Cs (A i) χ M.s p m (X i) i' (f i) b∧ Issue.Receipt (A i) M (X i))
variable (hR:∀ᶠ i in atTop, Ore M (X i) P)(h₁:p+2 ≤ m)(ha:Run atTop X f 0)(hk:k=m+1)(hμ:4≤ m)
variable (hv:∀ᶠ i in atTop,k ≤ (A i).post.p.order)(hP:∀ᶠ i in atTop,hatW (tip G P.L (X i))^4 ≤ (A i).f.val)
local notation "Y₀"=>fun i:ℕ=> tip G P.L (X i)
local notation "Q₀" i=> X i
local notation "v₀" i=> vol (Y₀ i)
local notation "W₀" i=> hull (X i)
local notation "Z!" i=> Issue.preModel (A i) χ p
local notation "θ" i=> Meauring.chart (A i).f G
local notation "Λ" i=> ((A i).F)
local notation "Yx" i=> 5*goalP (Y₀ i) p
local notation "α" i=> αm (X i)
local notation "L"=> (P.L.val:ℝ)
structure Ready (P:Patch)(M:StageCost) (m:ℕ)(A:ℝ):Prop where
   pos:0 < A
   high (j:ℕ) : j∈ Icc 4 m→climbP P M j < A
   low (j:ℕ) : j∈Icc 1 3→plotP P M j < A
variable {C:ℝ}(hK:Ready P M m C) (hσ:3 ≤ M.sway)(hN:6 ≤ M.s)
include hχ hp hq hX h hc hD hQ hR h₁ ha hk hμ hv hP hK hσ hN
noncomputable def RPos (A:Issue G)(p k m:ℕ)(χ:ChartRatio G)(x b:ℝ): Prop:= JetTab.RangeB (Measuring.chart A.c G) m (αm x) (hull x) (A.preModel χ p) k b ∧∀ i∈Metric.closedBall (0: Positions (Primary A.c G)) (hull x), ContDiffAt ℝ (↑(k+1:ℕ)) (A.preModel χ p) i
-- k derivative one higher.Rigidity.`hK2: threshold`.Marks shape.L top ballast.Enforce quant `cWidth`, `Cane`. volume.A.
set_option maxHeartbeats 500000 in
lemma extension : ∀ᶠ i in atTop,RPos (A i) p m M.s χ (X i) (C*goalP (X i) p):=by
    let y:=Y₀; let Gx(i):= goalP (X i) p; let D'(i):= goalP (y i) p; let Y(i):=5*D' i; have he:∀ᶠ i in atTop, FaceValue H' (y i) (A i).pre:= hp.mono (fun i hi=>by have hh:=hi.payments.case_; rwa [hi.space] at hh)
    have hf:Tendsto y atTop atTop:= (Work.E09.betaF_growth G P.L).comp hX; let n(i):=(A i).f; let w(i):=vol (Y₀ i); let V(i):= hull (X i); have hpw:Tendsto w atTop atTop:= (Alto.broad.comp hf).atTop_mul_const (r:=(32:ℝ)⁻¹) (by positivity)
    obtain ⟨c0,hc0,hT⟩:= anchors (n:=n) hf P D H' (fun i=>(A i).pre) J (fun i=>(A i).T) i' p hP he (hc.mono fun i h=> ⟨h.1.preT,h.1.pin0⟩) h hQ
    obtain ⟨y₀,b,h',hb⟩:= cold hX P D J χ H H' h hp hQ h₁ hk M i' _ hc hv ha -- `b` shadows
    obtain ⟨k1,hH,hg⟩:= Lodge.top_hat k; let F(i):= Lodge.masking (w i) Lodge.sea; let γ(i):= w i*k1; have hγ:Run atTop y γ 0:= ((Run.stanza hf|>.mulY hf _) |>.mulY hf _); have hF:∀ᶠ i in atTop,Lodge.Hat k (w i) (γ i) (F i)∧1 ≤ γ i:= (hpw.eventually_ge_atTop 1).mono fun i he=> ⟨Lodge.cool hg he, one_le_mul_of_one_le_of_one_le he hH⟩ -- w' notation replace
    have hx:= Issue.uniform χ J H H' P D h hD hQ hχ hX M i' hp hq hc hR h₁ ha hk (by omega) hμ F hF hγ
    let ε(i):=y i^stallN p; let p'(i):=duty (X i) m; let j(i):= closeN (y i); let Tz(k i):= (V i)^(k+1)*checkU (b i) (spire (p' i) M.s) (ε i) (αm (X i)) (p' i) (Fintype.card (Strand G)) M.s k (j i)
    have hE(k:ℕ): Tendsto (fun i=>Tz k i/Gx i) atTop (𝓝 0):=by
          have he:Run atTop X ε (stallN p):=(Run.wander hX G h ..).2 (Run.core hf _); have hξ:= Geneva.postPaid (k:=m) hX P.L h h' he 0 (Fintype.card (Strand G)) M.s k; let r(i):=(V i)^(k+1); have hr:Run atTop X r 0:= by let v':Run atTop X V 0:= Run.mulK hX (Run.mulY hX (Run.stanza hX) _) _; exact Run.Ypow hX v' _
          have hz:stallN p<pawn p:=by unfold stallN epsW; linarith only
          exact (hr.Ycost hX hξ).dory hX hz
    let Ω(i):= Cane.value (αm (X i)) M.C M.A M.E M.s M.sway; let α'(j i):= Tz j i+ (V i)^(j+1)*(Y i/(w i)^(j+1)*L^4*(Ω i/L)^(j+1)); have hi(j): Tendsto (fun i=> α' j i/Gx i) atTop (𝓝 (climbP P M j)):=by unfold α'; simp_rw [add_div]; simpa only [zero_add] using! ((hE j).add (climbs hX P j M h (p:=p)))
    obtain ⟨G',d,hpD,h_d,h0⟩:= Ruby.storie G k p; obtain ⟨A',Hq,hw⟩:= server hX χ J H H' P h hp M i' hc h₁ ha; let r(i):=(A i).fClock
    obtain ⟨u,v,vt,hvN,hv₀,he0⟩:=Issue.grants hX χ J H H' P D h hD hQ hχ hp hq (fun _=>0) (hp.mono (fun i hi=>by rw [norm_zero]; exact mul_nonneg zero_le_four (div_nonneg (sq_nonneg _) (by norm_num: (0:ℝ)≤32)) -- need
    )) (fun _=>0) (show 3 ≤ k from by omega) 1 1 (Eventually.of_forall (p:=fun i:ℕ=>0 ≤ (0:ℝ)) fun i=>le_refl _) (show Tendsto (fun _ : ℕ=>(0:ℝ)) atTop (𝓝 0) from tendsto_const_nhds) -- hi clearer
    let g(k i):= shortCash G k v (Y i) (αm (X i)) (V i) (w i) L (Ω i)
    let β(i' i):=volumeY G M.s i' (4-i') M.sway M.C M.A (αm (X i)) M.E P 0 (w i) (V i) (Y i) (slopeW (c0 i) (r i) 0 d (A' i) (Y i) (w i) p i' (n i) G)
    let q(i' i):= Tz i' i+(V i)^(i'+1)*g i' i+β i' i
    have hh (i)(hζ:i∈ Icc 1 3): Tendsto (fun k=> q i k/Gx k) atTop (𝓝 (plotP P M i)):=by
           have hz:Tendsto (fun k=> β i k/Gx k) atTop (𝓝 (plotP P M i)):= Geneva.volumeP hX P i M h hζ hP (fun s=> (Run.wander hX G h ..)|>.2 (hc0 s)) ((Run.wander hX G h ..)|>.2 ((roundS hX J H H' P h hp)|>.1)) Hq d -- signature
           unfold q; simp_rw [add_div]; simpa only [zero_add] using! (((hE i).add (sFire hX P i M h v (p:=p))).add hz)
    have hy: ∀ᶠ i in atTop,∀ j∈Icc 4 m, α' j i/Gx i≤ C:= (Icc 4 m).eventually_all.mpr (fun i hi' => (hi i).eventually (ge_mem_nhds (hK.high i hi')))
    have hm: ∀ᶠ i in atTop,∀ j∈ Icc (1:ℕ) 3, q j i/Gx i ≤ C:= (Icc 1 3).eventually_all.mpr fun i he=> (hh i he).eventually (ge_mem_nhds (hK.low i he))
    have hpX : ∀ᶠ i in atTop,0 < V i:= ((Alto.broad.comp hX).eventually_gt_atTop 0).mono fun i hi=> mul_pos (by norm_num : (0:ℝ)<4) (div_pos hi (by norm_num : (0:ℝ)<32))
    have hO:= tails hX J H H' P h hp; have h₂:= roundS hX J H H' P h hp
    filter_upwards [hy,hm,hx,hp,hq,hc, (dutyP hX M.s m).2.2.2.2,hb,hT,hR,hw,hF,hP,he0,hX.eventually_gt_atTop 1,hf.eventually_gt_atTop 1, hpX,hpw.eventually_ge_atTop 1, Issue.fat hX J H H' P h hp,cuff hf (hO.mono fun i hi=>hi.1),(h₂.1.bouquet hf (by norm_num)).eventually (ge_mem_nhds zero_lt_one), gate hX h hX P.L 0] with i hΨ hY hπ hp hD ⟨hW,hQr,hC,hB⟩ ⟨hρ,hα⟩ hb hv hR hc ⟨hK₁,hV₀⟩ hP hu hx hFt h₁ hω hm hr₀ hE_ hM
    let S:=A i; have hv₀:0< w i:=zero_lt_one.trans_le hω; have hz:S.passage (X i)= y i:=by unfold passage; rw [show S.S.patch=P from hp.space]; -- β link
    have hv1:(A i).passage (X i)= y i:=hz
    have ha:0 ≤ αm (y i):=(mul_nonneg (Nat.cast_nonneg _) hM.1.le).trans hM.2.1
    have hh:= hB.slope
    let T':=(A i).preModel χ p; let Ζ:=Metric.closedBall (0: Positions (Primary (A i).c G)) (hull (X i)); have h₆ : ∀ x∈Ζ,ContDiffAt ℝ k T' x:=fun x hx=> hb.2 x (mem_closedBall_zero_iff.mp hx)|>.price
    have hL(ℓ:ℕ)(h:ℓ ≤ m):=hQr.turns.peak ℓ h; have ht₀:= hQr.beam; have hV' := hQr.turns; rw [hv1] at ht₀ hV'; let D' := S.preY p; have h_run(j:ℕ)(he:j ≤ m): JetTab (Measuring.chart S.f G) (αm (y i)) M.s (w i) (closedBall 0 (w i)) D' j (Y i):= JetTab.levelAll hv₀ ha ht₀ hV' hμ le_rfl j he;
    have hχk:Lodge.Vase D' k (Y i) (w i):=by rw [hk]; exact Lodge.cs (fun j he=>h_run _ (by omega : j ≤ m)) ht₀ hω ha (by omega)
    have hl:L=(S.S.ratio.count.val:ℝ):=Nat.cast_inj.mpr ((congr_arg (fun i:Patch=>i.L.val) hp.space).symm); have hEq: αm (X i)/(S.S.ratio.count.val:ℝ) ≤ αm (y i):=by rw [← hl]; exact hm
    have hS := (pillars hX M.s _ hρ).2; have hp0 :0 < Gx i:=Real.rpow_pos_of_pos (zero_lt_one.trans hx) _
    have hp' :0 ≤ ε i:=Real.rpow_nonneg (zero_le_one.trans hFt.le) _; have hδ := hu.fast; let F':= (A i).F 
    have hz(x:Positions (Primary S.c G))(hx:x∈Ζ)(l:List (Primary S.c G))(ht:l.length ≤ m+1)(hb:l ≠[])(he:Bristol.peaks (Measuring.chart S.c G) l≤ j i): |buoy T' x l - Issue.phiB (A i) p x (F i) l|≤ ε i:=by refine hπ.1 x (mem_closedBall_zero_iff.mp hx) l hb (hk ▸ ht) ?_; rw [hp.space]; exact he
    have hF(k:Key S.F G): ((mold S.pre S.F S.v)⁻¹ k k) ≤ v:= (le_abs_self _).trans (hδ.growth.single (add_nonneg (le_refl _) (le_refl _)) _ _);
    refine ⟨⟨fun j hj=>?_⟩,fun x hx=>hk ▸ (h₆ x hx)⟩ -- `hk` rewrite.
    split
    next hv' =>
         by_cases he:j=0
         · have hr0:ContDiffAt ℝ k (Aqua.vine S.post S.fClock) 0:= by have ht := (h₆ 0 (Metric.mem_closedBall_self h₁.le)).add ((Aqua.pure (A i).post (A i|>.color χ) (A i).fClock p).contDiffAt.of_le le_top); simp only [T',Issue.preModel,film,Pi.sub_apply, sub_add_cancel] at ht; exact ht
           have hz:= Aqua.zen hW.postC.choose_spec hW.real1 hr0 (by omega) h
           subst j; apply JetTab.grant _ (mul_nonneg hK.pos.le hp0.le) h₁; intro g; rw [twillz]; change |fderiv ℝ (film (A i).post (color (A i) χ) S.fClock p) 0 (bolt g)| *_ ≤ _; rw [hz,_root_.zero_apply,abs_zero,zero_mul]; exact div_nonneg (mul_nonneg hK.pos.le hp0.le) (pow_pos h₁ _|>.le)
         obtain ⟨hpF,he'⟩:= hW.preT
         have hy : j∈ Finset.Icc 1 3:=mem_Icc.mpr ⟨Nat.pos_of_ne_zero he,by omega⟩
         let e' := ε i; have hb' : ∀ x ≤ m,∀ a∈Ζ,Roil (preModel S χ p) k (Alto.cWidth (X i)) a (b i):=fun q _ a hv=> hb.2 a (mem_closedBall_zero_iff.mp hv)
         have hSt:= shorter (A3:=A' i) F' S.pre S.v S.fClock S.ρ S.T (F i) S.M hW.critical hW.guessed hh hδ.bids hF T' hb' hz hEq hρ hα hS hK₁ hχk hk.ge hω h_run i' hb.1 ((pillars hX M.s _ hρ).1) h₁ hp' hσ hN hμ hW.real0 hv he' h hr₀ hE_ h0 ?_ ?_ j hy -- hp.g.A.Point.need
         · apply JetTab.cast hSt _ Set.Subset.rfl; refine le_trans (le_of_eq ?_) ((div_le_iff₀ hp0)|>.mp (hY j hy)); unfold q β Tz g; rw [show (A i).S.patch=P from hp.space]; unfold shortCash; rw [hl]; unfold V r n S Ω p'; have ht:0 < hull (X i):=h₁; field_simp; ring
         · intro l hl; have hp':=hc l hl|>.1.2; rw [hv1] at hp'; exact Tokew.delta (Tokew.soft hp' hM.2.2.1 ha) (by omega) le_rfl
         exact Nat.le_trans (by omega : 2≤3) (A i).S.patch.coarse
    next he=>
         have hp1:j∈ Finset.Icc 4 m:=mem_Icc.mpr ⟨le_of_not_gt he,hj⟩; have hb' : ∀ x ≤ m,∀ a∈Ζ,Roil (preModel S χ p) k (Alto.cWidth (X i)) a (b i):=fun q _ a hv=> hb.2 a (mem_closedBall_zero_iff.mp hv)
         have ht:= taller F' S.pre S.v S.fClock S.ρ S.T (F i) S.M hW.critical hW.guessed hh hδ.bids hF T' hb' hz hEq hρ hα hS hK₁ hχk hk.ge hω h_run hb.1 ((pillars hX M.s _ hρ).1) h₁ hp' j hj ; apply JetTab.cast ht _ Set.Subset.rfl -- sets already
         refine le_trans (le_of_eq ?_) ((div_le_iff₀ hp0)|>.mp (hΨ j hp1)); unfold α' Tz Ω V; rw [hl]; unfold p' S; ring
end YM.MSbar.Geneva
