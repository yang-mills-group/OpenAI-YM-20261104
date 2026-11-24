import YM.WilsonCoeffUV.Vacuum.UV.TopCosts
/-!
# Solved cutoff convergence bound without fixed-depth restriction

Same Levels (stamp demands on both sides, formal proof only). First over ALL
vacuum action and emitted positive scalar. Cover. Include reset ratios at other
meshes separately. Width aperture shifts and l¹ conversion downstream.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free Extension.UV.Linear PathCost Realm
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{n N M e m i k r b j l:ℕ}{U V W T :Credit}

lemma PairA.heavy {X:Type*}{s θ A B:ℝ}{P Q: Ten ℝ (Cloth X) j}(h:PairA s A (B*θ) P Q)(e:1≤ B): PairA s (A*B) θ P Q:= ⟨h.pose.le (le_mul_of_one_le_right h.nn e),h.vale.le (le_mul_of_one_le_right h.nn e), h.visit.le (le_of_eq (by ring))⟩
lemma post_end (g:G.Simple){A: Levels G}{Ñ:ChartRatio G}(h:LocalRatio Ñ)(p:m≤ N): shellK 2 (actionW A Ñ N m):= (catchment A Ñ g h p).rank
lemma post_near (g:G.Simple){A:Levels G}{Ñ:ChartRatio G}(h:LocalRatio Ñ)(p:m<N): shellK 2 (freshet A Ñ N m):= by
   intro i r x
   have ht:= (perch A Ñ g h p).growth i r
   apply ht.unique
   apply Yields.zero.congr; exact Eventually.of_forall fun n=> (winter_band _ _ _ _ _ h ((old A Ñ g h N _ p).basis _).lamp _ _ x).symm

-- startup descending rank bound trivial at many vacant sites
lemma vacant0 (hk:k+2< r): Traces G e U V k r:= by
    intro R m p b N M q h w
    let y:=R.depth _ p
    have he:= V.purchase y
    unfold Realm.Same horizonC; have H₁:= post_end (A:=R.draws) R.hG R.green (q.trans h) k r (by omega); have H₂:= post_end (A:=R.draws) R.hG R.green (q.trans w) k r (by omega)
    rw [H₁,H₂]; exact PairA.zero.up (zero_le_one.trans he) (trail_pos ..).le
lemma vanished (x:j=0 ∨ j=1): Traces G e U V i j:= by
   intro R m p b N M q h w
   have hf t (e:b≤ t): R.horizonC t m i j=0:= by
      have ht:= catchment R.draws R.paid R.hG R.green (q.trans e)
      rcases x with he|he
      · subst j; exact (congr_fun (congr_fun ht.empty i) 0).symm
      subst j; exact ht.vanishes i
   unfold Realm.Same; rw [hf _ h,hf _ w]; exact PairA.zero.up (zero_le_one.trans (V.purchase (R.depth _ p))) (trail_pos ..).le
lemma pristine (r:ℕ): Traces G e U (U.prodC (dome U)) 0 r:= by
   intro R m p b N M q h w
   let I:= R.mint m p
   have ht T (ha:b≤ T): R.horizonC T m 0 r=flatPal (plain G (freeForms R.draws T m)) 0 r:= congr_fun (catchment R.draws R.paid R.hG R.green (q.trans ha)).readout r
   have he:= (R.taxes _ p).freight
   have hp:= R.won p q
   unfold Realm.Same; rw [ht _ h,ht _ w, Realm.cash,Credit.products]
   exact (((kernel_pair (((I.cardG.kite b N M q h w).mono I.win.le).fee (Real.sqrt_nonneg _) he) 0 r).graded hp le_rfl).heavy ((dome U).purchase (R.depth _ p)))
lemma garnered (W k r)(p:∃T,Traces G e U T k r): ∃T,Traces G e U T k r ∧ ∀ y:ℝ,1≤y→ Credit.buy W y≤T.buy y:= by
   obtain ⟨V,hV⟩:= p; exact ⟨W.plus V,hV.more fun _ p=> Credit.thickened _ p,fun _ p=>Credit.thickens V p⟩
lemma amassed (h:k+1≤e)(hv:∀ i r, i< k+1 → Traces G e U V i r): ∃T, (∀ r,Traces G e U T (k+1) r)∧ (∀ y:ℝ,1≤y→Credit.buy V y≤T.buy y) := by
   suffices H : ∀ r ≤ k+1+3, ∃T, (∀ j,r≤j → Traces G e U T (k+1) j)∧ (∀ y:ℝ,1≤y→Credit.buy V y≤T.buy y) by obtain ⟨T,f,p⟩:= H 0 (by omega); exact ⟨T,fun i=> f i (by omega),p⟩
   intro i hi
   induction hi using Nat.decreasingInduction with
   | self=> exact ⟨V,fun i p=> vacant0 (by omega),fun _ _=>le_rfl⟩
   | of_succ r hk IH=>
     obtain ⟨W,hW,ht⟩:= IH
     have hw:∀ i j,lowerGrade i j (k+1) r → Traces G e U W i j:= by intro i j q; rcases q with q|⟨q,p⟩; exact (hv i j q).more ht; subst i; exact hW j p
     have hf : ∃T, Traces G e U T (k+1) r:= by
        by_cases H:2≤r
        · obtain ⟨d,rfl⟩:= Nat.exists_eq_add_of_le' H; have hl:d≤e:=by omega
          obtain ⟨u,p⟩:= recurring h hl (fun i j q=> (hw i j q).commands); exact tally_trace h hl hw p
        exact ⟨W,vanished (by omega)⟩
     obtain ⟨T,hT,he⟩:= garnered W _ _ hf
     refine ⟨T,fun i p=>?_,fun y hy=> le_trans (ht y hy) (he y hy)⟩
     rcases Nat.eq_or_lt_of_le p with b|b
     · subst i; exact hT
     exact (hW i b).more he

/-- All affine kernels in weighted sup at Native mesh, *uniform polynomial
cost* and power rate anchored even mid-window `m≤b≤N,M` against fine-end
changes. No premise at top boundary. Can upgrade fixed moment norm. -/
theorem full_vacuum (G:Gauge)(e:ℕ)(U:Credit): ∃T:Credit,∀ k≤ e,∀ r,Traces G e U T k r:=by
    suffices H: ∀ k≤ e,∃T:Credit,∀ j≤ k,∀ r,Traces G e U T j r from H e le_rfl
    intro k; induction k with
    | zero=> exact fun _=>⟨U.prodC (dome U),fun j h r=>Nat.eq_zero_of_le_zero h ▸ pristine r⟩
    | succ k IH=>
       intro h; obtain ⟨V,hV⟩:= IH (by omega); obtain ⟨T,hT,p⟩:= amassed h (fun i r h=>hV i (by omega) r)
       refine ⟨T,fun j hj r=>?_⟩
       rcases Nat.eq_or_lt_of_le hj with w|w; · subst j; exact hT r
       exact (hV j (by omega) r).more p

-- raw output and kinetic
variable (G e U)
def Trails (V: Credit)(i j:ℕ):= ∀ R: Realm G e U,∀ m (h:R.anchor≤m) b N M,m<b→ b≤N→b≤ M→ PairA (R.mint m h).σ (R.cash V m) (R.tempC m b) (freshet R.draws R.paid N m i j) (freshet R.draws R.paid M m i j)
variable {G e U}
lemma Trail_more {h:Trails G e U V i j}(p:∀ y:ℝ,1≤y→V.buy y≤W.buy y):Trails G e U W i j:= fun R m e b N M hv hp q=> (h R m e b N M hv hp q).up (p _ (R.depth m e)) (trail_pos ..).le
lemma trail_far (p:i+2<j): Trails G e U V i j:=by
    intro R m e b N M q h w
    rw [post_near R.hG R.green (show m<N by omega) _ _ (by omega),post_near R.hG R.green (show m<M by omega) _ _ (by omega)]
    exact PairA.zero.up (zero_le_one.trans (V.purchase (R.depth _ e))) (trail_pos ..).le
lemma trail_flower (p:k≤e)(hx:r≤ k+2)(hw:∀ i≤k,∀ r, Traces G e U W i r): ∃ V, Trails G e U V k r:=by
    let F:= jump U W
    let T:= (U.prodC (F.powC (outerD G k r))).prodC (doubling U)
    have hu: ∀ i j, lowerGrade i j (k+1) (k+3) → Traces G e U W i j:= by intro i j z; unfold lowerGrade at z; rcases z with a|a; exact hw i (by omega) j; exact vacant0 (by omega)
    refine ⟨T,fun R m h b N M z g t=>?_⟩
    let I:= R.mint m h
    let x:= R.cash F m
    let A:= U.prodC (F.powC (outerD G k r))
    let d:= R.cash (doubling U) m
    have hp:=R.depth _ h
    have hA:1≤ x:= Credit.purchase _ hp
    have hc: 1≤d:= Credit.purchase _ hp
    let θ:= d * R.tempC m b
    have he:= R.dominates_both h z
    let V:= I.readPast R.hG R.green x θ hA z g t he.1 he.2 (elderT R h z g t hu)
    have hb:= outer_price I.gear V r
    have hf:outerF k r I.gear*x^outerD G k r≤ R.cash A m:=by unfold Realm.cash A; rw [Credit.products,Credit.power]; exact mul_le_mul_of_nonneg_right ((R.taxes _ h).boom _ _ p (by omega)) (pow_nonneg (zero_le_one.trans hA) _)
    unfold Realm.cash T; rw [Credit.products]
    exact (hb.up hf V.θ).heavy hc

/-- Raw tinge with denominator scalar emitted. Fixed grade/rank, can
subsequently gather in finite alphabet. -/
theorem advent (G:Gauge)(e:ℕ)(U:Credit)(k r:ℕ)(p:k≤e):∃ V:Credit,Trails G e U V k r:=by
   by_cases h:r≤ k+2
   · obtain ⟨V,hV⟩:= full_vacuum G e U; exact trail_flower p h (fun i hi=>hV i (hi.trans p))
   exact ⟨U,trail_far (by omega)⟩
end YM.WilsonCoeffUV.Bank
