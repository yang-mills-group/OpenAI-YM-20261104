import YM.WilsonCoeffUV.Marked.Bounds.Independent
/-!
# Tuned slots above open, uncropped, LOG analytic estimates

Sampling same chart every S. Keeps every singleton incl unit jets. X profiles
part only enters after this. Transport full.
 -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Mark
open Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Metric Shard Realm PathCost
open Fountain Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {c f:Side}{ι α U V t:Type}{J K I T:Finset ι}{D k K':ι→ℕ}{i j i' j' a e r h N n m b l:ℕ}{G:Gauge}{σ τ u g B C z ρ:ℝ}{E W V' U':Credit}
variable [DecidableEq ι]
structure Origin (R:Realm G (e+1) E)(H:Hol G)(W V':Credit)(s:SealR G) where
    prest : PassportC H R s W V'
    width : ∀ i (h:R.anchor≤ i), (R.mint i h).σ ≤ (prest.f.arch.angle i (by rw [prest.tap]; exact h)).lamp.exitS
variable {R : Realm G (e+1) E}{H:Hol G}{Q:ι→SealR G}
abbrev Tribe (R:Realm G (e+1) E)(H:Hol G)(W V': Credit)(Q:ι→SealR G):= (s:ι)→ Origin R H W V' (Q s)

def centralL (A: Levels G)(L: ChartRatio G) (n m i:ℕ) (Q:SealR G)(X: Verse Q.F): TowerS G Q.D:= polarP A L Q.ans Q.path n m i X
def coatA (A: Levels G)(L: ChartRatio G)(n m:ℕ)(Q:ι→SealR G)(X:(s:ι)→ Verse (Q s).F) : Outerm G (fun s=>(Q s).D):= open Classical in fun p J=> if h:J.card=1 then
   let s:=Classical.choose (Finset.card_eq_one.mp h)
   let T:=cn (fun i=>(Q i).D) s (centralL A L n m n (Q s) (X s)) (p s)
   let H:J={s}:=Classical.choose_spec (Finset.card_eq_one.mp h); H.symm ▸ T else 0
lemma coatLeaf (A:Levels G)(L:ChartRatio G)(n m:ℕ)(Q:ι→SealR G)(X:(s:ι)→ Verse (Q s).F)(p s): coatA A L n m Q X p {s}=cn (fun i=>(Q i).D) s (centralL A L n m n (Q s) (X s)) (p s):=by
   unfold coatA; split
   next h=>
       have hz : Classical.choose (Finset.card_eq_one.mp h)=s:= ((Finset.singleton_inj).mp (Classical.choose_spec (Finset.card_eq_one.mp h))).symm;
       have hv (s':ι)(v:s'=s): (show ({s'}:Finset ι)={s} from v ▸ rfl) ▸ cn (fun i=>(Q i).D) s' (centralL A L n m n (Q s') (X s')) (p s') = cn (fun i=>(Q i).D) s (centralL A L n m n (Q s) (X s)) (p s):=by subst s'; rfl
       exact hv _ hz
   next h=> exact False.elim (h (Finset.card_singleton _))
lemma coatLazy (A:Levels G)(L:ChartRatio G)(n m:ℕ)(Q:ι→SealR G)(X:(s:ι)→ Verse (Q s).F)(p J)(h:J.card≠ 1): coatA A L n m Q X p J=0:=dif_neg h

def WinterMark (H:Hol G)(Q:SealR G)(e:ℕ)(E W V X: Credit): Credit:= (((polarExp H Q.ans Q.path e E W V).choose.usingC (Credit.leanC.plus Credit.leanC)).prodC X)
def sprouted (Q:SealR G)(X:Verse Q.F)(e:ℕ)(x:ℝ):Prop:=∀ j≤ e,∀ t:Alma Q.F,‖coeff j (X t)‖≤x

lemma charted (s:SealR G)(t: Origin R H W V' s)(X: s.Rider)(q:m ≤ i)(v:i≤ N)(a':R.anchor≤ m)(b:R.y m≤z)(U:Credit) (p:sprouted s X e (U.buy z))(h:j≤e)(r:ℕ): Cork Bank.terrain 0 (R.mint i (a'.trans q)).σ ((WinterMark H s e E W V' U).buy (z+snowP R.draws.S m i)) ((centralL R.draws R.paid N m i s X).2 j r):=by
   let P:=t.prest; let T:= (polarExp H s.ans s.path e E W V').choose; let L:=P.f.arch; let S:=R.draws.S; have hv:L.V.anchor ≤ m:= by change P.f.arch.V.anchor≤m; rw [P.tap]; exact a';
   let x:=z+snowP S m i; have hS:0≤ snowP S m i:=sub_nonneg.mpr (scales S q); have hm:S=L.V.draws.S:= Eq.symm (congr_arg Levels.S P.lands)
   have hz:1≤z:=(R.depth m a').trans b; have hx:z≤x:= le_add_of_nonneg_right hS; have he (i):L.V.y i=R.y i:=congr_fun P.depths _
   let Z:=(Credit.leanC.plus Credit.leanC).buy x; let V:= U.buy z; have hV:=U.purchase hz
   have ht:Compar L.V.draws.S L.V.y m i≤ Z:=by
       have hU:= winterH S q; refine le_trans ?_ (Credit.fuel _ _ (hz.trans hx)); simp_rw [Credit.lean_cost]; unfold Compar x; unfold snowP at hU ⊢; rw [←hm,he]; linarith only [hU,b,hz]
   rw [show centralL R.draws R.paid N m i s X=centralL L.V.draws L.V.paid N m i s X from (by rw [show L.V.draws=R.draws from P.lands,show L.V.paid=R.paid from P.modes])]
   refine ((Cork.mono ?_ (t.width _ (a'.trans q))) : Cork _ _ _ (T.buy Z*V) _).cost ?_
   · exact (polarExp H s.ans s.path e E W V').choose_spec t.prest.f m i N X V Z hv q v ht (zero_le_one.trans hV) p j h r
   unfold WinterMark; rw [Credit.products,Credit.stock_up]; apply mul_le_mul_of_nonneg_left (U.elder hz hx) (zero_le_one.trans (T.purchase (Credit.purchase _ (hz.trans hx))))

section
variable (P: Tribe R H W V' Q)(X:(s:ι)→ Verse (Q s).F) (paceM:R.anchor≤m)
include P paceM
omit [DecidableEq ι] in
private lemma fired (v:m ≤ i)(g:i≤ N)(s:ι): On (Q s).h (centralL R.draws R.paid N m i (Q s) (X s)):=by rw [← (P s).prest.lands, ← (P s).prest.modes]; exact tournure (P s).prest.f.arch _ ((P s).prest.tap.symm ▸ (paceM.trans v)) g
lemma cloister (v:m≤ N): Wellness (fun i=>(Q i).h) (coatA R.draws R.paid N m Q X) :=by
    refine ⟨fun p=>coatLazy _ _ _ _ _ _ _ _ (by simp), fun p S=>?_,fun p q S z=>?_⟩
    · by_cases hp:S.card=1; · obtain ⟨x,rfl⟩:= Finset.card_eq_one.mp hp; rw [coatLeaf,mass,Finset.sum_singleton]; exact ((On_auth (fired P X paceM v le_rfl x)).tuft (petal (fun i=>(Q i).D) x)).shifted _
      rw [coatLazy _ _ _ _ _ _ _ _ hp]; exact unstamped
    by_cases hp:S.card=1; · obtain ⟨x,rfl⟩:= Finset.card_eq_one.mp hp; rw [coatLeaf,coatLeaf,z _ (by simp)]
    rw [coatLazy _ _ _ _ _ _ _ _ hp,coatLazy _ _ _ _ _ _ _ _ hp]
lemma opened (v:m≤ N)(p:m≤ i)(b:i≤N)(w:ι→ Cover)(s:ι):
   let k(s:ι):= (Q s).h
   Gears R.draws R.paid k k N N i (coatA R.draws R.paid N m Q X) w {s}=cn (fun i=>(Q i).D) s (centralL R.draws R.paid N m i (Q s) (X s)) (w s):=by
   intro k; induction b using Nat.decreasingInduction generalizing w with
   | self=> rw [gearTop,coatLeaf]
   | of_succ i h ih=>
        rw [gearUp _ _ _ h]; have hp:= Cog R.draws R.paid (K':=k) le_rfl _ (cloister P X paceM v) R.hG R.green (show i+1≤ N from h)
        have hq :m ≤ i+1:=p.trans (by omega)
        rw [rawSc R.hG R.green h s hp w _ (fired P X paceM hq h s) (fun z=>ih hq z)]
        apply congr_arg (fun X=> cn _ s X (w s)); rw [← (P s).prest.lands,← (P s).prest.modes]; exact summerUp (P s).prest.f.arch _ ((P s).prest.tap.symm ▸ paceM) p h
end
variable [Fintype ι]
lemma dictated (H:Hol G)(Q:ι→SealR G)(E W V' U:Credit)(e:ℕ): ∃ V:Credit,∀ (R:Realm G (e+1) E)(_P:Tribe R H W V' Q)(m N:ℕ)(X:(s:ι)→ Verse (Q s).F)(z:ℝ),R.anchor≤ m → m≤ N→ R.y m≤z → (∀ s, sprouted (Q s) (X s) e (U.buy z)) → Borealis R (fun i=>(Q i).D) (fun i=>(Q i).h) (fun i=>(Q i).h) (coatA R.draws R.paid N m Q X) m N V z :=by
   let K s:= WinterMark H (Q s) e E W V' U
   obtain ⟨V,hV⟩:=uniformPays (P:=fun s T=>∀ x:ℝ,1≤ x →(K s).buy x≤ T.buy x) Finset.univ (fun s _=> ⟨K s,fun _ _=> le_rfl⟩) (fun _ _ _ _ p h y t=> (h y t).trans (p y t))
   refine ⟨V,fun R P m N X z u v w h=>⟨cloister P X u v,fun S f x=>coatLazy _ _ _ _ _ _ _ S (by omega),u,w,fun i x g b s l z' r=>?_⟩⟩
   rw [opened P X u v g b x s]; simp only [Finset.card_singleton,pow_one]; have hz:1≤z+snowP R.draws.S m i:= ((R.depth m u).trans w).trans (le_add_of_nonneg_right (sub_nonneg.mpr (scales _ g)))
   -- budget pen
   apply Wig.more (Budges _ s _ (R.mint i (u.trans g)).width.le _ (charted _ (P s) (X s) g b u w U (h s) z' r)); exact hV s (Finset.mem_univ s) _ hz
end YM.WilsonCoeffUV.Wheel.Mark
