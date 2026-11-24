import YM.WilsonCoeffUV.Stable.Analytic.Captured
import YM.WilsonCoeffUV.Emit.PhysicalClock
/-!
# Simultaneous appointment on same SAME chart/calendar

Length and cost choices once for all finite eventual demands. No premise that a given
E1 witness already satisfies these stronger terms. Numbers on a true leased path history.
Useful with StableStrip.received,mask prebills can join at W and P. Not stabilizing the
analytic strip of a g-capture evaluated answer in its physical coupling; only cost-wise.
E controllers align patterns R.Finance' along identical algebraic spool at b..j; one producer for
linear pre maps in Polk, the other producers R and Y can use their canonical tickets from
physical appointments at SAME clock. They need not have identical Revenue/Gear fields as these
are quantitative upper bound choices only, not algebraic definitions of D.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.WilsonCoeffUV.StableStrip
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Supply Ticket Polestar Next.Foundations Shard Plan Mer Mer.Patrol Wheel Wheel.Mark
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{H:Hol G}{R:Master H}{A A':Levels G}{p0:Sheet G}{Q:Supply.Rolls p0}{Ω:Protection Q}{X:ℕ→ℕ} {Y:Delays Ω}{o:Bar Y}{B:Supply.Wait o}{Ñ:ChartRatio G}{k h D u i e j m:ℕ}
lemma set_charges (H:Hol G)(R: Master H)(g:G.Simple)(hA:LocalRatio Ñ)(p:Paid B A)(x:h<D)(s: Tendsto X atTop atTop)(v:Rails h k u e)(f:AwardsM H R X Q Ñ Y)
    (F:(fun i=>rootRise H R Ñ p0.kernel i (X i))≤p0.floorL)
    (P:(fun i=>rootPost H R Ñ p0.kernel i (X i) (Q.L i))≤Y.betaEntry) :
    ∀ᶠ m:ℕ in atTop, ∃ W:ChorusLine H (R.T h) x e Credit.leanC Credit.leanC Credit.leanC, W.arch.V.draws=A ∧ W.arch.V.paid=Ñ ∧ W.arch.V.y=zz A∧ W.arch.V.anchor=m∧(∀ i (p':W.arch.V.anchor≤ i), ∃ z:5 ≤ A.clock.J (i+1),lampp W.arch i p'=crestM A i z)∧ RootDeal W.arch k Credit.leanC ∧ Weston W.arch Credit.leanC ∧ ∃ T:Torch H (R.T h) x v Credit.leanC Credit.leanC Credit.leanC,T.L=W.arch:=by
   have he: Tendsto (fun i=>A.clock.J (i+1)) atTop atTop:= A.fits.deep.comp (tendsto_add_atTop_nat 1)
   obtain ⟨t,h'⟩:= eventually_atTop.mp ((he.eventually_ge_atTop (h+5)).and ((s.comp he).eventually_ge_atTop (e+1+D+k+u))); apply (eventually_ge_atTop t).mono; intro i q
   have hv j (u':i≤ j):= h' j (q.trans u')
   obtain ⟨W,C,S,sK,g',B',L⟩:= figures H R g hA f.ink f.rise (F':=X) (D':=X) p f.fg f.hg f.rg x (e:=e) (m:=i) (fun j t=> by have hx:=hv j t; simp only [Function.comp_apply] at hx; omega)
   have hm :∀ j, A.S.block j = Q.L (A.clock.J (j+1)):=by intro j; rw [←A.fits.sameFactor,p.lengths]
   have he' (j:ℕ)(x':W.arch.V.anchor≤ j): RootPre H (R.F h) x k e (W.arch.angle j x') ∧ RootAfter H (R.T h) x k e (W.arch.angle j x') (W.arch.V.cash Credit.leanC j)∧ CompassP H (R.T h) x v (W.arch.angle j x') (W.arch.V.cash Credit.leanC j):=by
      have hy:=hv j (g' ▸ x'); simp only [Function.comp_apply] at hy
      obtain ⟨x0,y,z,t',h0⟩:= L j x'; let u':=A.clock.J (j+1); have hf: h<D:= x
      have h1: rootRise H R Ñ p0.kernel u' (X u')≤ (A.S.block j).val:= by rw [hm]; exact (F u').trans (Q.large u').need
      have h2: rootPost H R Ñ p0.kernel u' (X u') (A.S.block j) ≤ Real.exp (Real.exp (zz A j-1)):=by rw [hm]; exact (P u').trans ((booked g p f.fg i).pays j (g' ▸ x'))
      obtain ⟨A',C⟩:= onLedger H R Ñ p0.kernel u' (X u') A j p.kernel rfl y z t' x0 h1 x (by unfold u'; omega) (show k≤X u' from by unfold u'; omega) (show e≤X u' from by unfold u'; omega) h2
      rw [h0,Realm.cash,sK,Credit.lean_cost]; refine ⟨A',C,PackingCash H R Ñ p0.kernel u' (X u') A j p.kernel rfl y z t' x0 ?_ x v ?_ ?_ ?_ ?_ ?_⟩; · rw [hm]; exact (f.carve _).trans (Q.large u').need
      all_goals try first | (unfold u'; omega) | (rw [hm]; exact (f.page u').trans ((booked g p f.fg i).pays j (g' ▸ x')))
   refine ⟨W,C,S,sK,g',fun j p=>?_ ,⟨v.hk,fun j p=>(he' j p).1,fun j p=>(he' j p).2.1⟩,B',⟨W.arch,fun j p=>(he' j p).2.2⟩,rfl⟩; obtain ⟨x,a,z,y,h⟩:= L j p; unfold lampp; rw [h]; exact ⟨a,rfl⟩

open YM.WilsonCoeffLease Physical
-- compose pre/post requests into those for Physical.issuedTogether
abbrev expFloor (G:Gauge)(F:ℕ→ℕ)(P:Prepaid0 G): Prepaid0 G:=fun K=> (fun i=>rootRise (hol G) (primes G) (chart G) K i (F i))⊔P K
def expPost (G:Gauge)(F:ℕ→ℕ)(P:Funds0 G):Funds0 G:=fun s Q Ω=>
     let T:= P s Q Ω
     { T with betaEntry:= (fun i=>rootPost (hol G) (primes G) (chart G) s.kernel i (F i) (Q.L i)) ⊔ T.betaEntry }
variable {L:KernelChoices}{C:Family G}{P:Prepaid0 G}{T:Funds0 G}{Z:ℕ→Gear G→ℝ}
lemma paidSoft (hS:Leased C L (Physical.moreL G X (expFloor G X P)) (Physical.later G X Z (expPost G X T))) (g:G.Simple)(x:h<D)(s: Tendsto X atTop atTop)(v:Rails h k u e):
    ∀ᶠ m:ℕ in atTop, ∃ W:ChorusLine (hol G) ((primes G).T h) x e Credit.leanC Credit.leanC Credit.leanC, W.arch.V.draws=C.path.levels ∧ W.arch.V.paid=chart G ∧ W.arch.V.y=zz C.path.levels∧ W.arch.V.anchor=m∧(∀ i (p':W.arch.V.anchor≤ i), ∃ z:5 ≤ C.path.levels.clock.J (i+1),lampp W.arch i p'=crestM C.path.levels i z)∧ RootDeal W.arch k Credit.leanC ∧ Weston W.arch Credit.leanC ∧ ∃ T:Torch (hol G) ((primes G).T h) x v Credit.leanC Credit.leanC Credit.leanC, T.L=W.arch:=by
   obtain ⟨A,Q,v',z⟩:= paid_clock hS; obtain ⟨F,W,y⟩:= early hS; have hv:expFloor G X P hS.page.kernel ≤ hS.page.floorL:=by rw [hS.same]; exact W
   apply set_charges (hol G) (primes G) g (chart_ok G) hS.proof x s v (reported (hol G) (primes G) F Q) (sup_le_iff.mp hv).1 (sup_le_iff.mp A.beta).1
lemma stillPaid (hS:Leased C L (Physical.moreL G X (expFloor G X P)) (Physical.later G X Z (expPost G X T))) : P L ≤ hS.page.floorL ∧ Push.PriceCompiler.DelayLe (T hS.page hS.phases hS.cert) hS.delays:=by
   let z:= paid_clock hS; exact ⟨(sup_le_iff.mp (early hS).2.1).2, ⟨(sup_le_iff.mp z.1.beta).2,z.1.scale,z.1.shells,z.1.growth⟩⟩
end YM.WilsonCoeffUV.StableStrip
