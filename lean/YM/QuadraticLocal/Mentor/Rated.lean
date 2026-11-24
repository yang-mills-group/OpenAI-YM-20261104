import YM.QuadraticLocal.Travel
import YM.QuadraticLocal.Tides
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Mentor
open Function Filter Finset Wilson Lattice RG Pressure Marker
open PhysicalNext PhysicalNext.Repeat AnalyticBridge.VerifiedReset Progress.DirectedRecipe
open Next.Scheduling ConnectedActivityE6 Push Push.SectorMeasure Push.AbsoluteSums SliceRows
open RemainderComparison Lyric Muse Creek Travel
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{P:Teller G} (Q:ConnectedActivityE6.Target G P)
variable (Y:Stage) -- use P.top P.below automatically
set_option quotPrecheck false
local notation "tq"=> (P.top.supportExponent)
local notation "v"=> (P.below.order)
local notation "τ"=> (P.below.supportExponent+1+1)
local notation "Δ"=> (P.below.power)
variable {κ A W n:ℝ}
local notation "σ"=> Chi.canonical
/-!
 # Precise power-factor hiring Eyes. Same as Beaming.Summer, including γ witnesses
   before choosing test dimensions and Holder arity etc. Inherits K schedule expense; keep
   force and mask lenders plus purchase an occupied scanner for each *possible* marker-subgroup
   on an AUX footing. These curves can be used to produce the post-load estimates, no volume
   (for all P.Paid including Price.C.Cost Old). Enrollment here doesn't automatically register
   these costs on stamp occurrences (needs actual Epoch certificate on supplied trajectory).
-/
abbrev capDay:ℝ:= 16
def SummerPlus (k s:ℕ)(T:ℝ→ℝ) (U V γ:ℝ→ℝ)(W μ:ℝ)(L:Side) (o:ConnectedActivityE6.Target.Order G W) {F:Postage} (Y:Time.Forecast F)(x:ℝ) : Prop:=
    ∀ (c f:Side) (S:StepData c f) (D:Tube G S), SliceRows.Stamp D → ∀ (R:Rep G f)(P':Rep G c) (C:ℝ) (H:Cash W x μ L Q o C D R), Next.Scheduling.inBand (betaF G x L) R.beta→ Time.Same P.top R.p → Time.Same P.below P'.p → P'.p.B=radiusB x→
      R.p.B ≤ 2*P'.p.B → P'.p.threshold=Pressure.temp x → ∃ Eye:Eyes H P' (Y.pair.strong (betaF G x L) R.beta/8) (V x) (U x) (T x) k, Eye.height=s∧ k≤ Eye.sight∧Eye.moves=1 ∧ Eye.σ=0 ∧ Eye.γ= γ x
lemma qualifies (hp:3/8+Q.rate<0) (hq:τ<Q.exp): ∃ n:ℕ,∀ L:Side,n≤L.val→∀ W μ,0<W→0<μ→∀ k (s:ℕ),1≤ s→∀ (o:ConnectedActivityE6.Target.Order G W)(F:Postage)(Y:Time.Forecast F)(T:ℝ→ℝ),Reserve G L T→Y.hard ≤ μ/32→∃ U V Γ,Reserve G L U ∧ Reserve G L V∧ Reserve G L Γ ∧ ∀ᶠ x in atTop,SummerPlus Q k s T U V Γ W μ L o Y x:=by
    obtain ⟨ℓ,hℓ⟩:= Muse.generation Q hp; obtain ⟨w,hw⟩:= Lyric.bidLift (Q:=Q) («v»:=tq) (show Q.ε+2*Q.ε≤tq from by linarith only [Q.grants.1,Q.usable]) Q.usable
    obtain ⟨b,hb⟩:= ((tendsto_natCast_atTop_atTop (R:=ℝ)).atTop_mul_const P.top.price_pos|>.eventually_ge_atTop (20*τ*Extra.Multi.tilePrice 0))|> eventually_atTop.mp -- Stage.price_pos?
    refine ⟨ℓ+w+b,fun L hL W μ hW hμ k s hS o F Y T hT hY=>?_⟩
    by_cases h: ∃ (D:Patch), D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j
    swap
    · refine ⟨fun _=>1,fun _=>0,fun _=>0, Reserve.const _,Reserve.const _,Reserve.const _,Eventually.of_forall fun x c f S D hd R P' C H=>False.elim ?_⟩
      have ht:= H.laws.data.funds; exact h ⟨S.patch,ht.funds.kernel,ht.length_eq,ht.funds.atStep⟩
    obtain ⟨D,hd,hr,hy⟩:= h
    let ε:=(Q.exp-τ)/2; have he : 0<ε:=by unfold ε; linarith only [hq]; -- r(f) for old matte at exciting high, currently feed constant 0.B.Spirit. Can announce nonzero through strengthening when applying Moon.Role.
    obtain ⟨U,V,C',E,q,hU,hV,hC,hE,hq,h⟩:= hℓ L (by omega) D hd W μ o hW hμ σ v Δ k s τ ε 1 (by linarith only [P.below.price_pos]) he (by unfold ε; linarith) zero_lt_one T (fun _=> k+Fintype.card (Site L)) (fun _=>0) 0 hT (Reserve.const _) ((Reserve.const _).rate)
    refine ⟨U,V,C',hU,hV,hC,?_⟩; filter_upwards [h, Willow.allot_in P Q L μ F Y hY] with x Hx hv c f S T' hT R P' C H hX h0 h1 hp he ht
    obtain ⟨a,ha⟩:=Hx c f S T' (H.laws.data.funds.patch hr hy) hT R C H
    have he': S.ratio.count=L:= H.laws.data.funds.length_eq; let U':= P'.p.order; have hf: U'=v:= h1.2.1;
    -- choose cast by padding notation. Introduce local vars as rewriting dependent. `Pad` order argument not passed into Coat Budget etc.
    have hg : ∃ A:Pad H P'.p.order σ,Roles H σ A k s P'.p.power (k+Fintype.card (Site L)) (P'.p.supportExponent+1+1) 1 ε (T x) 0 (U x) (V x) (C' x) (E x):=by -- shadow C reserve saved name
       rw [h1.2.1,h1.1, h1.2.2]; exact ⟨a,ha⟩
    obtain ⟨a',ha'⟩:=hg; refine ⟨⟨_,ε,1,0,_,_, s,a',ha',hp,ht,(show Fintype.card (Site S.ratio.count)≤ k+Fintype.card (Site L) from (by rw [he']; omega)),he,?_,h0.2.2.symm ▸ hw L (by omega),hv R.beta hX s hS⟩,rfl,Nat.le_add_right .., rfl,rfl,rfl⟩
    rw [he', h0.2.2,h1.2.2]; exact hb L.val (by omega)
section funding
open Input RG.Supply Precision
structure Salary (G:Gauge)(L:Side) where
    enroll : ℝ→ℝ
    price : ℝ→ℝ
    γ : ℝ→ℝ
    hU : Reserve G L enroll
    hV : Reserve G L price
    hγ : Reserve G L γ
abbrev SummerS (Q:ConnectedActivityE6.Target G P)(k s:ℕ)(W μ:ℝ)(L:Side)(o:ConnectedActivityE6.Target.Order G W) {F:Postage} (T:Time.Forecast F) (certs:Salary G L)(t:ℝ) : Prop:= SummerPlus Q k s (fun _=> capDay) certs.enroll certs.price certs.γ W μ L o T t
-- choose once per Π Runtime.Hour. Post authorize at every Width etc.CalendarΚ.
open Push.PriceCompiler
variable {S:Sheet G}{K:MapPrices} (C':Targets S K)
def Institute (m:ℕ→ℕ):= ∀ x y, StepStages x y →∀ L:Side,m x ≤ L.val→∀ W μ,0<W→0<μ→∀ (o:ConnectedActivityE6.Target.Order G W)(F:Postage)(A:Time.Forecast F), A.hard≤ μ/32 → ∀ (k s:ℕ),1≤ s→∃ certs: Salary G L,∀ᶠ t in atTop,SummerS (C' x y) k s W μ L o A certs t
lemma leases (hf:∀ x y,StepStages x y→3/8+(C' x y).rate<0)(ht:∀ x y, StepStages x y → (S.profile y).supportExponent+1+1 < (C' x y).exp) : ∃ m:ℕ→ℕ, Institute C' m := by
 have hk(x y:ℕ): ∃ d:ℕ,∀ (_ : StepStages x y) (L:Side),d ≤ L.val→∀ W μ,0<W→0<μ→∀ (o:ConnectedActivityE6.Target.Order G W)(F:Postage)(A:Time.Forecast F), A.hard≤ μ/32 → ∀ (k s:ℕ),1≤ s→∃ certs: Salary G L,∀ᶠ t in atTop,SummerS (C' x y) k s W μ L o A certs t:= by
    by_cases h:StepStages x y; swap; · exact ⟨0,fun hE=> (h hE).elim⟩
    obtain ⟨L,hL⟩:= qualifies (C' x y) (hf x y h) (ht x y h); refine ⟨L,fun _ z hz W μ hW hμ o F A hA k s hs=> ?_⟩
    obtain ⟨x,y,Z,hx,hy,hZ,hℓ⟩:= hL z hz _ _ hW hμ k s hs o F A _ (Reserve.const capDay) hA; exact ⟨⟨x,y,Z,hx,hy,hZ⟩,hℓ⟩
 choose n hn using hk; refine ⟨fromMax n,fun i j hD L hp=> hn i j hD L ((le_fromMax n hD).trans hp)⟩
end funding
end YM.QuadraticLocal.Mentor
