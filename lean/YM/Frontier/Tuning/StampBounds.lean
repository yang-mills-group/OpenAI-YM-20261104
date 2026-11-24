import YM.Frontier.Tuning.Voice
set_option autoImplicit false
noncomputable section
namespace YM.Frontier.Tuning.Voice
open Function Filter Set Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Bid Reserves Ursell Trees
open ConnectedActivityE6 Shell Channel SliceRows Control Window Census Mask Pulse Itinerary Coat
open Packets Presented Sector Raw ProbabilityTheory Poll Pond ComplexVertex GaussContour LocalContour
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical ENNReal
variable {G : Gauge} {P : Teller G} {c f n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {α t e d g : ℝ} {ι : Type*} {R:Rep G f} {Q Q': YM.ConnectedActivityE6.Target G P}{C x μ W:ℝ}{o:Target.Order G W} {L:Side}
-- type includes placeholder v? `vk` remove from Critical later.

abbrev fairWith (p : Stores S→ℝ) (a b: LogIndex c f→ℝ) (s:ℕ→ℝ) (l B : ℕ) : Head S→ℝ:=
    Mixed.costs S l B p (rates s a (topStorm S.patch)) -- b unused
abbrev paidWith (p:Stores S→ℝ)(a:LogIndex c f→ℝ)(s:ℕ→ℝ)(q:ℝ)(l B:ℕ) : Head S→ℝ :=
    Mixed.costs S l B p (rates s a q)
lemma combineWith (f : Stores S→ℝ)(a b s) {q A:ℝ} (l B:ℕ)(K:Molecule S) (hq:0≤A)(ha:A*topStorm S.patch ≤ q)(hh:∀ i,0≤fairWith f a b s l B i):
    A^(blaze K).card* ∏ i∈K,fairWith (S:=S) f a b s l B i ≤ ∏ i∈K,paidWith f a s q l B i:= by
   rw [cumulate K, cumulate K,cumulate K.toRight, cumulate K.toRight, cumulate K.toRight.toRight, cumulate K.toRight.toRight]
   change _ * ((∏ i∈K.toLeft,fairWith f a b s l B (Sum.inl i))*((∏ i∈K.toRight.toLeft,s i)*((∏ i∈K.toRight.toRight.toLeft,a i)* ∏ _i∈ blaze K,topStorm S.patch)))≤ _
   -- frequencies
   change _ ≤ ((∏ i∈K.toLeft,fairWith f a b s l B (Sum.inl i))*((∏ i∈K.toRight.toLeft, s i)*((∏ i∈K.toRight.toRight.toLeft, a i)* ∏ _i∈ blaze K,q)))
   simp only [prod_const]; rw [mul_left_comm, mul_left_comm _ (∏ i∈K.toRight.toLeft, _), mul_left_comm _ (∏ i∈K.toRight.toRight.toLeft, _), ← mul_pow]
   have h1 : 0≤∏ i∈K.toLeft, fairWith (S:=S) f a b s l B (.inl i):= prod_nonneg fun i _=>hh _
   have h2 : 0≤∏ i∈K.toRight.toLeft, s i:= prod_nonneg fun i _=>hh (.inr (.inl i))
   have h3 : 0≤∏ i∈K.toRight.toRight.toLeft, a i:= prod_nonneg fun i _=>hh (.inr (.inr (.inl i)))
   exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hq ((zero_le_one.trans (topStorm_one _)))) ha _) h3) h2) h1
   -- nonneg A*topStorm may be negative when A negative; add hA assumption; use ha0

structure SheetEstimate (H : Cash W x μ L Q o C T R) (Q' : YM.ConnectedActivityE6.Target G P) (b' : ℝ) where
  ve : LogIndex c f→ℝ
  de : ℕ→ℝ
  dk : ℕ→ℝ
  warningPaid : ℝ
  height : 0<b'
  caps : Critical (x:=x) R T b' o.a o.K Q.table ve de de dk
  halo : Q'.halo=Q.halo

namespace SheetEstimate
variable {v l : Payload G f}{b θ:ℝ}{X:Coat T F}{H : Cash W x μ L Q o C T R} (E : SheetEstimate H Q' b)
abbrev packet' (E : SheetEstimate H Q' b) (β:ℝ) : Stores S→ℝ:=steamP S (Q'.costs L μ β x C)
abbrev costsAt β:=fairWith (E.packet' β) (logPrice E.ve E.de) E.ve E.dk Q.halo (radiusB x)
abbrev pricesAt β:=paidWith (E.packet' β) (logPrice E.ve E.de) E.dk E.warningPaid Q.halo (radiusB x)
-- exponents/head marks table-independent
lemma packet'_raw β : E.packet' β = steamP S (Q.costs L μ β x C):=rfl
include H
variable (X) {z:ℂ}(hx:X.x=x)(hk:X.width=o.K)(hm:X.manifest)(hz:z.re∈Set.Icc (b/2) (2*b))(ht: ‖z‖ ≤ 2*b)(hn: Nonempty (Cash W x μ L Q o C T (resetBeta R z.re)))
include hx hk hm hz ht hn
set_option maxHeartbeats 400000 in
lemma vertex_price (w:Air f G) (hv:BoundAt R v l E.de E.dk) k (i:Head S):
    ‖rawCvertex X R v l Q.table z W o.a k Q.halo w i‖ ≤ costsAt E z.re i * Sum.elim (fun i' : Stores S=> Real.exp (massPower X i'*Real.log (‖z‖/z.re))) (fun _=>1) i:=by
   obtain ⟨N⟩:=hn
   rcases i with A|a|a|a
   · change ‖rawCvertex X (resetBeta R z.re) v l Q.table z W o.a k Q.halo w (Sum.inl A)‖ ≤ _
     apply (pack_exact X (resetBeta R z.re) Q.table o.a (G:=G) (S:=S) (T:=T) (F:=F) (B:=X.B) A rfl k W Q.halo l v w (lt_of_lt_of_le (half_pos E.height) hz.1) rfl Q.table_exists.scale).trans
     exact mul_le_mul_of_nonneg_right (N.voice X hx hk hm k (Sum.inl A) (heat z.re w)) (Real.exp_nonneg _)
   · dsimp only [rawCvertex, Sum.elim, Mixed.costs, rates, costsAt, fairWith]; rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (X.conserve ..).1, mul_one]
     change ‖l a _‖* _ ≤ _; apply (mul_le_mul_of_nonneg_right (hv a _).2 (X.conserve ..).1).trans (mul_le_of_le_one_right (E.caps.pays a) (X.conserve ..).2)
   · dsimp only [rawCvertex,Sum.elim,costsAt,Mixed.costs,rates,fairWith]; rw [mul_one]; exact E.caps.logBound X hx hk hm ht hv
   dsimp only [rawCvertex,Sum.elim,costsAt, Mixed.costs, rates, fairWith]; rw [Complex.norm_real,mul_one]; exact X.fires_at ..
lemma price_pos (hv: BoundAt R v l E.de E.dk) (i:Head S) : 0 ≤ E.costsAt z.re i:=by
   have hh:= (norm_nonneg _).trans (vertex_price (X:=X) E hx hk hm hz ht hn (0) hv (∅) i)
   rcases i with i|i
   · exact nonneg_of_mul_nonneg_left hh (Real.exp_pos _)
   rw [Sum.elim_inr, mul_one] at hh; exact hh
lemma emerging_price (s:Molecule S) k w (hv:BoundAt R v l E.de E.dk) :
    ‖∏ i∈s, rawCvertex X R v l Q.table z W o.a k Q.halo w i‖ ≤ (∏ i∈s, E.costsAt z.re i) * Real.exp ((∑ i∈s.toLeft,massPower X i)*Real.log (‖z‖/z.re)):=by
   rw [norm_prod]; exact (prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>vertex_price (X:=X) E hx hk hm hz ht hn w hv k i)).trans_eq (by rw [prod_mul_distrib,cumulate s (Sum.elim _ _),sum_mul,Real.exp_sum]; simp only [Sum.elim_inl,Sum.elim_inr,prod_const_one,mul_one])
omit E H hx hk hm hz ht hn
lemma detector_alarm (H' : Cash W x μ L Q o C T (resetBeta R z.re)) (w : Air f G) (hz:0<z.re) (hx':X.x=x)(hk:X.width=o.K)(hm:X.manifest) (s: Molecule S) k :
    ∀ ⦃v l⦄,(∏ i∈s,rawCvertex X R v l Q.table z W o.a k Q.halo w i)≠0 → heat z.re w ∈ X.catastrophe o.ξ z.re (blaze s):=by
    intro v l ht
    have hu:= (H'.quotes F X hx' hk hm).2.2.2 (blaze s)|>.2 k (heat z.re w)
    refine hu (fun i hi hf=> ht <| Finset.prod_eq_zero (mem_toRight.mp (mem_toRight.mp (mem_toRight.mp hi))) ?_)
    change (X.detect (world X w) W o.a R k i:ℂ)=0
    rw [← ComplexVertex.restores X hz];exact Complex.ofReal_inj.mpr hf
lemma spill_alarm (X : Coat T F)(P' : Finset (Tubular f G)) (x : Finset (WarningAt c f)) (β:ℝ) (s t : Air f G)(a : ℝ) (hA: 0<a*X.t*(gStep β)⁻¹) :
    s=spill P' (swim P' t) → s∈X.catastrophe a β x → t∈ X.catastrophe a β x := by
   rintro rfl h j hj;obtain ⟨i,hp,h⟩:=h j hj; refine ⟨i,hp,?_⟩
   by_cases he:i∈P'
   · convert h using 1; unfold spill; simp [he,swim]
   refine False.elim (not_lt.mpr h ?_); simpa [spill,he] using hA


lemma measure_fold (X : Coat T F) (Q' : Finset (Tubular f G))(a : Finset (WarningAt c f)) (K : Cash W x μ L Q o C T (resetBeta R z.re))(hp:X.relating.PosDef)
       (hA:0<o.ξ*X.t*(gStep z.re)⁻¹)(hx:X.x=x)(hk:X.width=o.K)(hm:X.manifest) : (arch Q' X.relating).real (spill Q' ⁻¹' X.catastrophe o.ξ z.re a) ≤ K.alarms^a.card:=by
   have hSet : MeasurableSet (X.catastrophe o.ξ z.re a):= Poll.sounded ..
   have hMeasure : MeasurePreserving (swim Q') X.dice (arch Q' X.relating) := orbit hp.posSemidef Q'
   have hZ : swim Q' ⁻¹' (spill Q' ⁻¹' X.catastrophe o.ξ z.re a) ⊆ X.catastrophe o.ξ z.re a := fun y hy=> spill_alarm X Q' a z.re _ y _ hA rfl hy
   rw [Measure.real,← MeasurePreserving.measure_preimage hMeasure ?_]
   · exact le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hZ)) ((K.quotes F X hx hk hm).2.2.2 a).1
   · exact (hSet.preimage (spill_m Q')).nullMeasurableSet
include E H hx hk hm hz ht hn
lemma scaledBody {X':Coat T F} (K:Cash W x μ L Q o C T (resetBeta R z.re)) (rI:X.relating=X'.relating)(hT:X.t=X'.t)(hB:X.B=X'.B) {Q0:Finset (Tubular f G)}(k:Molecule S) l' (hv:BoundAt R v l E.de E.dk)(hA:K.alarms*topStorm S.patch ≤ E.warningPaid):
    (rebate (circuit Q0 X'.relating) (fun w => ∏ i∈k,rawCvertex X R v l Q.table z W o.a l' Q.halo (spill Q0 w) i) z.re) ≤
       Real.exp ((∑ i∈k.toLeft,massPower X i)*Real.log (‖z‖/z.re)) * ∏ i∈k,E.pricesAt z.re i := by
   let M := Real.exp ((∑ i∈k.toLeft,massPower X i)*Real.log (‖z‖/z.re))
   have hM:0 ≤ M:=by unfold M; positivity
   let J := (spill Q0) ⁻¹' X.catastrophe o.ξ z.re (blaze k)
   have hS:MeasurableSet J:= (show MeasurableSet (X.catastrophe o.ξ z.re (blaze k)) from Poll.sounded ..).preimage (spill_m Q0)
   let f w:= ∏ i∈k,rawCvertex X R v l Q.table z W o.a l' Q.halo w i
   have hp:= (H.laws.data.localP F X hx hk hm).sails.fullC
   let ν := arch Q0 X'.relating
   have hz0 :0<z.re:= lt_of_lt_of_le (half_pos E.height) hz.1
   have hPos (i):0≤costsAt E z.re i:=E.price_pos (X:=X) hx hk hm hz ht hn hv i
   let P:= ∏ i∈k,E.costsAt z.re i; have hP: 0 ≤ P:= prod_nonneg fun i _=>hPos i
   have hw (y): ‖f (spill Q0 ((Real.sqrt z.re)⁻¹ • y))‖ ≤ J.indicator (fun _=> M*P) y :=by
      by_cases hx0:y∈J
      · rw [Set.indicator_of_mem hx0]; exact (E.emerging_price (X:=X) hx hk hm hz ht hn k l' (spill Q0 ((Real.sqrt z.re)⁻¹ • y)) hv).trans_eq (mul_comm _ _)
      rw [Set.indicator_of_notMem hx0, show f (spill Q0 ((Real.sqrt z.re)⁻¹ • y))=0 by apply not_ne_iff.mp; intro hn; have hT:=detector_alarm (X:=X) K _ hz0 hx hk hm k l' hn; rw [scales_cancel Q0 z.re y hz0] at hT; exact hx0 hT,norm_zero]
   rw [rebate_eq _ (rI ▸ hp|>.submatrix Subtype.val_injective)]
   let a := fun w=>‖f (spill Q0 ((Real.sqrt z.re)⁻¹ • w))‖
   change (∫ w,a w ∂ν) ≤ _
   suffices (∫ w,a w ∂ν) ≤ M*P* K.alarms^(blaze k).card by
     refine this.trans ((le_of_eq (by rw [mul_right_comm,mul_right_comm,mul_assoc M P,mul_comm P _])).trans ?_)
     exact mul_le_mul_of_nonneg_left (combineWith _ _ _ _ _ _ _ K.pos hA hPos) hM
   by_cases hi:Integrable a ν
   · refine (integral_mono hi ((integrable_const _).indicator hS) hw).trans ?_; rw [integral_indicator_const _ hS]; rw [mul_comm (M*P)]
     apply mul_le_mul_of_nonneg_right _ (mul_nonneg hM hP)
     unfold ν J; rw [←rI]
     exact measure_fold X Q0 _ K hp (mul_pos (mul_pos o.rare (by unfold Coat.t; rw [hx];exact H.laws.data.room.fiery)) (inv_pos.mpr (show 0<gStep z.re from inv_pos.mpr (Real.sqrt_pos.mpr hz0)))) hx hk hm
   rw [MeasureTheory.integral_undef hi]; exact mul_nonneg (mul_nonneg hM hP) (pow_nonneg K.pos _)
end SheetEstimate
end YM.Frontier.Tuning.Voice
