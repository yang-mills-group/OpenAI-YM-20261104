import YM.OPE.Compatible.Scrape.Scud
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Pill
open Function Filter Set MeasureTheory Lattice RG Wilson Source Labels Push.Local Next.Foundations
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{X:Type*}{n:Side} {i j k:ℕ}{Fr:Frame G k} (T:SectionData Fr){V:Rep G n} (o:Site n){A:Hol G}{t a b c:ℝ}
local notation "F"=> Config G n
variable {P:Coefficient Fr n}
variable {r:ℕ}
lemma OriC (h:T.Sound A)(hp:P.Format o A V)(hb:P.remBound o V a b)(X:Support n)(hv:T.footprint o⊆ X)(hx:Crop V o r⊆ X)(ε:ℝ)(he:0<ε)(hV:V.p.Regular (T.footprint o) (presented T o V.p.threshold P.x)) (hP:V.p.supBounds o (T.footprint o) (presented T o V.p.threshold P.x) t):∃ f:F→ℂ,
     V.p.Regular X f ∧ V.p.supBounds o X f (t+b) ∧ Reads A o X (0:Label G k) (f-(presented T o V.p.threshold P.x)) ∧
       ∀ U:F,Healthy V.p.threshold X U→ ‖P.exponentialEntry o T V U-f U‖≤ ε+Real.exp (-V.p.supportExponent*r)*b:=by
     obtain ⟨I,hI,hu⟩:= chargesM o hp hb r ε he; let f:= presented T o V.p.threshold P.x; let g : F→ℂ:=∑ i∈I,P.regular i; have hh(i)(hj:i∈I): P.support i⊆X:= fun x he=>hx (hI i hj he); obtain ⟨hk,hg⟩:= heightsX o hp X I hh hb; let q:= regular_larger hV hv; refine ⟨f+g,regular_add q hk,bound_add q hk (bound_larger hP hv) hg,?_,fun U hU=>?_⟩
     · change Reads A o X (0:Label G k) (f+g-f); rw [add_sub_cancel_left]; exact totalsW o hp X I hh
     let y:= fun i=> P.maskedTerm V i U; change ‖(primary T o V.p.threshold P.x U + ∑' i, y i) -(f U+g U)‖≤ _; rw [presented_primary o h _ U (Finset.disjoint_of_subset_left hv hU), show g U=∑ i∈I,y i from ?_]; change ‖f U+_-(f U+_)‖≤_; rw [add_sub_add_left_eq_sub]; exact hu U
     unfold g; rw [Finset.sum_apply]; refine Finset.sum_congr rfl fun i hi=> (masked_eq _ _ _ _ (show Healthy _ (P.support i) U from Finset.disjoint_of_subset_left (hh i hi) hU)).symm
section
variable {M:Type*}{l:Filter M}{β:M→ℝ}{C:M→Side}(Rv:(i:M)→ Rep G (C i)){α b s:M→ℝ}{Θ:M→Support n}
-- B purchases, no monotone. Cap supportEXP lower
abbrev CropScore (β:M→ℝ)(i:M):= Nat.ceil (Counters β i^2)
lemma clampR (h:Tendsto β l atTop)(hp:Receipt β l (fun i=>((Rv i).p.B:ℝ))) : Receipt β l (fun i=> (clump (Rv i).p (CropScore β i):ℝ)) :=by
     have hu := carth h; have hf:= (sans h).power 2 hu|>.ceiling hu (Eventually.of_forall (fun i=>sq_nonneg _))
     unfold clump; push_cast; exact (hf.product (((Score.steady (4:ℝ) hu).product hp).plus (Score.steady (2:ℝ) hu) hu)).plus ((Score.steady (2:ℝ) hu).product hp) hu
lemma cough (h:Tendsto β l atTop){δ:ℝ}(hp:0 < δ)(hx:∀ᶠ i in l, δ ≤ (Rv i).p.supportExponent): Wick β l (fun i=>Real.exp (- (Rv i).p.supportExponent*CropScore β i)):=by
       intro q; refine RateLE.transfer (Wick_bill h hp q) ?_; filter_upwards [hx] with i hi; rw [Real.norm_of_nonneg (Real.exp_nonneg _),Real.norm_of_nonneg (show 0 ≤ Burl δ (Counters β) i from Real.exp_nonneg _),Burl,neg_mul,neg_mul]; apply Real.exp_monotone; apply neg_le_neg; exact mul_le_mul hi (Nat.le_ceil _) (sq_nonneg _) ((Rv i).p.exponent_pos.le)
structure Meets (P:(i:M)→ Coefficient Fr (C i))(A:Hol G)(a b s :M→ℝ)(X: (i:M)→ Support (C i)):Prop where
       earnings i : (P i).Format 0 A (Rv i)
       rem i : (P i).remBound 0 (Rv i) (a i) (b i)
       calm i : (Rv i).p.Regular (T.footprint (0:Site (C i))) (presented T 0 (Rv i).p.threshold (P i).x)
       cash i : (Rv i).p.supBounds 0 (T.footprint (0:Site (C i))) (presented T 0 (Rv i).p.threshold (P i).x) (s i)
       visor i : T.footprint 0 ⊆ X i
variable {P:(i:M)→ Coefficient Fr (C i)}{g:ℕ}{X:(i:M)→ Support (C i)}
lemma Skin (hp:Meets T Rv P A α b s X)(hf:T.Sound A)(h:Tendsto β l atTop)(hd:Wax β l b t)(δ:ℝ)(hq:0<δ)(hy:∀ᶠ i in l,δ≤ (Rv i).p.supportExponent)(he:∀ i,Crop (Rv i) (0:Site (C i)) (CropScore β i)⊆ X i):∃ f:(i:M)→ Config G (C i)→ℂ, ∃ ε:M→ℝ, Wick β l ε ∧∀ i,
       (Rv i).p.Regular (X i) (f i) ∧ (Rv i).p.supBounds 0 (X i) (f i) (s i+b i)∧ Reads A 0 (X i) (0:Label G k) (f i-presented T 0 (Rv i).p.threshold (P i).x) ∧∀ U:Config G (C i), Healthy (Rv i).p.threshold (X i) U→ ‖(P i).exponentialEntry 0 T (Rv i) U-f i U‖≤ ε i:=by
       choose f H using fun i=> OriC T (0:Site (C i)) hf (hp.earnings i) (hp.rem i) (X i) (hp.visor i) (he i) (Burl δ (Counters β) i) (Real.exp_pos _) (hp.calm i) (hp.cash i); refine ⟨f,fun i=> Burl δ (Counters β) i+ _ ,fun j=>?_,H⟩; exact (Wick_bill h hq j).add (((cough Rv h hq hy (j-t)).mul hd).mono (by rw [sub_add_cancel])) (carth h)
end
end YM.OPE.Pill
