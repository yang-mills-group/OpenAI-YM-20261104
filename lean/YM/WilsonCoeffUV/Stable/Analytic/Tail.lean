import YM.WilsonCoeffUV.Stable.Analytic.Step
/-!
# Fine-end strip receipts through D product

Like Stable/AllHeights (bloom_all) but in the true exponential coefficient costs; remains stable
also over long soft window k..j with coupling measured locally at transmitted end.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.WilsonCoeffUV.StableStrip
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Shard Shard.Ore
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{ι U V: Type*}{r h D l j i e k a m b u N M c:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A C t B x δ:ℝ}

def rootSteps (H:Hol G)(T:SectionData F)(p:h<D) (k i r:ℕ):ℕ:= (analyticStep F H T p k i r).choose
def rootExpense (H:Hol G)(T:SectionData F)(p:h<D) (k i r:ℕ)(I:Cloister G h): ℝ:= ((analyticStep F H T p k i r).choose_spec I).choose

-- usable before block size choice. Proof below in Stable/Analytic/Budget.
def RootPre (H:Hol G)(F:Frame G h)(p:h<D)(k e:ℕ)(I:Cloister G h):Prop := ∀ r≤ k+e, I.lamp.dues r ∧ velo H F p I.lamp r/(inkPin I).patch.L.val ≤ Real.exp (-Real.log (inkPin I).patch.L.val/2)
def RootAfter (H:Hol G)(T:SectionData F)(p:h<D)(k e:ℕ)(I:Cloister G h)(x:ℝ):Prop := ∀ i≤e,∀ r≤ k+e,rootExpense H T p k i r I≤ x
structure RootDeal {H:Hol G}{T:SectionData F}{p:h<D}{E W:Credit}(L:Theatre H T p e E W)(k:ℕ)(K: Credit): Prop where
    dom : h ≤ k
    floor i (p':L.V.anchor ≤ i): RootPre H F p k e (L.angle i p')
    posted i (p':L.V.anchor ≤ i): RootAfter H T p k e (L.angle i p') (L.V.cash K i)
variable {E W K X Y: Credit}{H:Hol G}{T:SectionData F}{p:h<D}
abbrev lampp (L:Theatre H T p e E W)m h:= (L.angle m h).lamp.exitS
lemma offer_peaks (L:Theatre H T p e E W)(ha:L.V.anchor≤m)(hb:m<b)(hn:b≤N)(hv:b≤M)(hi:i≤ e)(r:ℕ):
    let V:=L.V; let I:=inkPin (L.angle m ha); let X:=(allPlays H T p e E W).choose
    let Q:= (jump E (full_vacuum G (e+1) E).choose).plus X
    ∃ R:Rally (i+1) 0 I, R.σ= V.cash (doubling E) m * V.tempC m b ∧ R.x=V.cash Q m ∧ ClaimP V.draws N m (hb.trans_le hn) V.hG V.green (V.mint m ha) I R.P ∧ ClaimP V.draws M m (hb.trans_le hv) V.hG V.green (V.mint m ha) I R.Q ∧∀ j v,v≤ i→ Shelf Bank.terrain 0 (lampp L m ha) R.x R.σ ((L.lore N m).2 j v r) ((L.lore M m).2 j v r):=by
   intro V I X Q; have hy:=V.depth _ ha; have hu:= elderT (k:=i+1) (j0:=0) V ha hb hn hv (fun i j v=>(full_vacuum G (e+1) E).choose_spec i (by unfold lowerGrade at v; omega) j)
   let H':=V.cash (doubling E) m * V.tempC m b; have he:= V.dominates_both ha hb; have hs : V.tempC m b≤ H':=le_mul_of_one_le_left (trail_pos ..).le (Credit.purchase (doubling E) hy); have hH:0≤ H':= (trail_pos ..).le.trans hs
   obtain ⟨R,h,h',q,q'⟩:= garageC V.draws V.paid (V.mint m ha) _ V.hG V.green hb hn hv (Q.purchase hy) he.1 he.2 (show (V.mint m ha).runs (i+1) 0 H' (V.cash Q m) N M from fun i j r=> (hu i j r).up (Credit.thickens _ hy) hH) (L.effort m ha)
   refine ⟨R,q',q,⟨(L.effort m ha).1,h⟩,⟨(L.effort m ha).1,h'⟩,fun j v t=>?_⟩
   rw [q,q']; have hh:= (allPlays H T p e E W).choose_spec v (valence F j) r (t.trans hi) L m ha b N M hb.le hn hv j rfl; exact (show Shelf Bank.terrain 0 _ _ H' _ _ from ⟨hh.wax,hh.wane,hh.toll.cost (mul_le_mul_of_nonneg_left hs hh.nn)⟩).step (Credit.thickened _ hy) hH

def taxCharge (H:Hol G)(T:SectionData F)(p:h<D)(e k i r:ℕ)(E W K:Credit):Credit:= K.prodC (((jump E (full_vacuum G (e+1) E).choose).plus (allPlays H T p e E W).choose).powC (rootSteps H T p k i r))
lemma rootStep (L:Theatre H T p e E W)(t:RootDeal L k K)(ha:L.V.anchor≤m)(hv:m<N)(u':i≤e)(z:r≤k+e):
    let V:=L.V
    ∀ P:TowerS G D,On k P→ opal F P=0→∀ X A:ℝ, Twig 0 (lampp L (m+1) (by omega)) X (P.2 i r)→0≤A→(∀ i' j,lowerGrade i' j i r→Twig 0 (lampp L (m+1) (by omega)) A (P.2 i' j)) →
     Twig 0 (lampp L m ha) (Real.exp (-arc V.draws.S m/2)*X + V.cash (taxCharge H T p e k i r E W K) m*A) ((Sink V.draws V.paid T p N m k P).2 i r):=by
    intro V P w he X A f a hp; let I:=L.angle m ha; obtain ⟨R,g,h',s,_,q⟩:= offer_peaks L ha hv (le_refl N) (le_refl N) u' r
    obtain ⟨Z⟩:= (L.effort m ha).2 N hv _ _ _ s.2; let D':= rootSteps H T p k i r
    obtain ⟨hD,ht⟩:= t.floor m ha r z
    apply Cork.cost (((analyticStep F H T p k i r).choose_spec I).choose_spec.2 V.draws V.paid N m R hv V.hG V.green _ s hD P w he (production L hv.le ha).1 Z (fun i j h=>(q i j h).wax) X A a (Cork.mono f (L.touch m ha)) (fun i j v=> Cork.mono (hp i j v) (L.touch m ha)))
    have hm:(inkPin I).patch.L=V.draws.S.block m:= by rw [s.1]; rfl
    refine add_le_add (mul_le_mul_of_nonneg_right (ht.trans_eq (by rw [arch,show (inkPin (L.angle m ha)).patch.L = _ from hm])) f.1) ?_
    apply mul_le_mul_of_nonneg_right _ a; unfold taxCharge cash; rw [Credit.products,Credit.power]; have h:= R.rich; change rootExpense H T p k i r I* R.x^D'≤ _; rw [h'] at h ⊢; exact mul_le_mul_of_nonneg_right (t.posted _ _ i u' r z) (pow_nonneg (zero_le_one.trans h) _)

lemma strip_closed (L:Theatre H T p e E W)(h0:L.V.anchor≤m)(p':m≤c)(hp:c≤N)(hk:h≤k)(Y:TowerS G D)(P:On k Y)(q:opal F Y=0): let X:=breaths L.V.draws L.V.paid T p N k c m Y; On k X∧opal F X=0:=by
    induction p' using Nat.decreasingInduction with
    | self=> rw [breath_top]; exact ⟨P,q⟩
    | of_succ i he ih=> obtain ⟨x,-⟩:=ih (by omega); rw [breath_step _ _ T p _ he]; apply Sink_for _ _ _ _ (production L (he.le.trans hp) h0).1 hk (he.trans_le hp) L.V.hG L.V.green x

def stripHeight (F:Frame G h)(e k:ℕ)(s A:ℝ)(Y:TowerS G D): Prop:= On k Y ∧ opal F Y=0 ∧ 0≤ A ∧∀ i r,i≤e → Twig 0 s A (Y.2 i r)
def stripPeak (H:Hol G)(T:SectionData F)(p:h<D)(e k:ℕ)(E W K B:Credit)(i r:ℕ): Prop:=∀ a:Theatre H T p e E W,RootDeal a k K→∀ m (_:a.V.anchor≤m) c N (p':m≤c), c≤N→∀ P:TowerS G D,∀ A,stripHeight F e k (lampp a c (by omega)) A P → let L:= a.V; Twig 0 (lampp a m (by assumption)) (L.cash B m*L.tempC m c*A) ((breaths L.draws L.paid T p N k c m P).2 i r)
lemma stripPeak.more (X':stripPeak H T p e k E W K X i r) (h:∀ y:ℝ,1≤y→ X.buy y ≤ Y.buy y): stripPeak H T p e k E W K Y i r:= by
   intro a u m h' c N t x P A q L'; exact Cork.cost (X' a u m h' c N t x P A q) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (h _ (a.V.depth _ h')) (trail_pos ..).le) q.2.2.1)
lemma stripAway (h': k+i<r): stripPeak H T p e k E W K X i r:=by
   intro a u m z c N y w P A q' L; have hy:=L.depth m z
   rw [solo_shape (strip_closed a z y w u.dom P q'.1 q'.2.1).1 i r h']; exact Cork.zero.cost (mul_nonneg (mul_nonneg (zero_le_one.trans (X.purchase hy)) (trail_pos ..).le) q'.2.2.1)

lemma strip_tower (p': i≤ e) (h': r≤k+i)(hv:∀ i' j,lowerGrade i' j i r→stripPeak H T p e k E W K X i' j): ∃ C:Credit, stripPeak H T p e k E W K C i r:=by
   have ht:r≤ k+e:=by omega
   let B:= taxCharge H T p e k i r E W K; let Y:= jumped E X; let C:= B.prodC Y
   refine ⟨C.behind,?_⟩; intro a u m x c N y w P A q L; let R:= a.V; have hx:= R.depth m x; let F' m:=breaths R.draws R.paid T p N k c m P
   have hA:= q.2.2.1
   suffices hh : ∀ i'≤c, ∀ z:a.V.anchor ≤ i', Twig 0 (lampp a i' z) (C.tower Credit.liftA (R.y i')*R.tempC i' c*A) ((F' i').2 i r) by exact Cork.cost (hh m y x) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Credit.donation C _ _ _ hx) (trail_pos ..).le) hA)
   intro m hm; induction hm using Nat.decreasingInduction with
   | self=> intro he; unfold F'; rw [breath_top]; exact Cork.cost (q.2.2.2 i r p') (purchase_border C R he hA)
   | of_succ m g ih=>
      intro h
      let V:=F' (m+1); let t:=R.tempC m c
      have hh:a.V.anchor≤ m+1:=by omega
      have H := ih hh; have hy: ∀ i' j,lowerGrade i' j i r → Twig 0 (lampp a (m+1) hh) (R.cash Y m * t * A) (V.2 i' j):= fun i j v=> Cork.cost (hv i j v a u (m+1) hh c N g w P A q) (mul_le_mul_of_nonneg_right (lift_money R h X c) hA)
      have ht':0≤t:= (trail_pos ..).le; obtain ⟨s,hX⟩:= strip_closed a hh g w u.dom P q.1 q.2.1
      rw [show F' m=Sink R.draws R.paid T p N m k V from breath_step _ _ T p P g]; apply Cork.cost (rootStep a u h (g.trans_le w) p' ht V s hX _ _ H (mul_nonneg (mul_nonneg (zero_le_one.trans (Y.purchase (R.depth _ h))) ht') hA) hy)
      exact le_trans (le_of_eq (show _ + _= Real.exp (-arc R.draws.S m/2)*(C.tower Credit.liftA (R.y (m+1))* R.tempC (m+1) c*A)+R.cash C m*R.tempC m c*A from congr_arg (fun y=> Real.exp (-arc R.draws.S m/2)*(C.tower Credit.liftA (R.y (m+1))*R.tempC (m+1) c*A)+y) (show R.cash B m*(R.cash Y m*t*A)=R.cash C m*t*A by unfold C cash; rw [Credit.products]; ring))) (aging C R h c A hA)

theorem exponentialStable (H:Hol G)(T:SectionData F)(p:h<D)(e k:ℕ)(E W K:Credit): ∃ X:Credit,∀ i≤e,∀ j, stripPeak H T p e k E W K X i j:=by
    refine seasonsPaid (fun i j V=>stripPeak H T p e k E W K V i j) k e ?_ (fun i j v _=>stripAway v) (fun i j A B t p=> p.more t)
    intro i hv r V hf; by_cases h:r≤k+i
    · exact strip_tower hv h hf
    exact ⟨V,stripAway (by omega)⟩
end YM.WilsonCoeffUV.StableStrip
