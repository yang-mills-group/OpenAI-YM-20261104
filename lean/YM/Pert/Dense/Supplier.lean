import YM.Pert.Dense.Portal

/-! Use the granular provider on *every* drift to infinity on the trimmed stages. Same field map for all the tested moments at that tick (not one map per scalar condition), conditional only as in setup, no extraction change when passing to an existing ordered trajectory (see `harvested`). Auer-clock arcs may depend on horizons. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Dense
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec Supply PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Climb Ward Next.UVStress
open YM.MergeProof YM.MergeProof.East
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{Θ:Sheet G} (B:MapPrices) {L:Rolls Θ}{E:Protection L}{H:Delays E}{Z:Bar H}
variable {O₀ : HaarBudget G} {J₀ : ChartRatio G} {U:Wait Z}
open StationPort
variable {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{μ:ℕ→ℕ}

structure Reaches (C:Family G)(n m:ℕ)(r:ℝ) (S:Table C.book) (h:S.Hierarchy) (h' : (standard C).RealSpin) (R ε:ℝ) : Prop where
  panel : ∃ U: Next.UVStress.Panel S, -- names conflict
     (∀ d : ℕ, d ≤ m → StraightAt h.spin h' U d) ∧ U 0 ((standard C).unit 0)=S.unit 0 ∧
     ∀ (k : ℕ), k ≤ n → ∀ v : Fin k → (standard C).Tag,(∀ i,(v i).1 ≤ m) → ∀ t : Test k,
       tsupport t ⊆ Scaling.window R k → ∀ M : ℝ,0 < M → (∀ x, ‖t x‖ ≤ M) →
       ‖t.applyTo (Next.UVStress.tested r U v)-t.applyTo (Ward.disc v)‖ ≤ ε * Next.UVStress.Station.charge v * M
-- property is independent of Binding so it belongs to the same physics endpoints.
structure OnPath (U:Wait Z)(C:Family G) : Prop where
   reports : ∃ arc:ℕ→ℝ, (∀ d,d+6≤arc d) ∧ ∀ h' :(standard C).RealSpin,(standard C).Smooth→ ∀ d (N) (R:ℝ),N ≤ d+2→ 0<R→∀ F:Extraction.Order,
    ∀ S:Table C.book, ∀ h : S.Hierarchy, F.Ordered C S → F.PointLimits C S → ∀ ε:ℝ,0<ε→ ∀ᶠ i:ℕ in atTop,Interior U C.path.levels i → Reaches C N d (gap C.path.levels (arc d) i) S h h' R ε
variable {L' : ∀ N p m:ℕ, m<N → GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)} {p : StationPort U B O₀ J₀}
variable {K : Binding C} (hp:p.Certified) (hg:G.Simple) (hk:Paid U C.path.levels) (hm:K.prices=B)
   (hC:C.Makes)(hE:ParadeX C)(hS:Scrim C W u ψ φ δ (fly C.path.levels) μ L')
local notation "A" => C.path.levels
local notation "S" => standard C

include hp hg hk hm hC hE hS
set_option maxHeartbeats 2000000
lemma podium_seq (F:Extraction.Order) (R:ℝ) (hr:0<R) (hs:(S).Smooth) (h':(S).RealSpin)
    (d:ℕ)(f:ℕ→ℕ)(he:Tendsto f atTop atTop) (hh:∀ i,Interior U (A) (f i)) :
    ∃ c, ∃ Y:ℕ→ℕ→ℕ→TableL C d,∃ k, Granular (fun i=>wok C d (f (i+k)) (p.arc d) c (Y i)) F h' (d+2) R := by
    have hQ := he.eventually (hp.orders C hk K hm hC hE d)
    obtain ⟨k,hk⟩ := Filter.eventually_atTop.mp (hQ.mono (fun i hi=>hi (hh i)))
    have hE(i):=hk (i+k) (Nat.le_add_left k i)
    choose Y hY using hE
    let θ:=p.panels d
    obtain ⟨c,hsigns⟩:=hp.signs d -- don't shadow
    let V(i):=wok C d (f (i+k)) (p.arc d) c (Y i); have hx(i) := MergeProof.East.w_right c F h' (p.arc d) (hY i)
    have he : Tendsto (fun i=>f (i+k)) atTop atTop := he.comp (tendsto_atTop_mono (f:=fun i=>i) (g:=fun i=>i+k) (fun i=>Nat.le_add_right i k) tendsto_id)
    refine ⟨c,Y,k,?_,(Station.gap_rate (A) hg _).comp he,?_⟩
    · exact ⟨Eventually.of_forall (fun i=>(hx i).1), Eventually.of_forall (fun i=> (hx i).2.mono fun j h=> h.mono fun k h=>h.1),
           Eventually.of_forall (fun i=> (hx i).2.mono fun j h=> h.mono fun k h=> h.2.1),
           Eventually.of_forall (fun i=> (hx i).2.mono fun j h=> h.mono fun k h=> h.2.2)⟩
    intro m h'k t ht x
    exact MergeProof.East.aspect θ K hC hg hS O₀ J₀ _ (hp.reasonable d) F (Nat.le_add_left ..) R hr hs h' hsigns t ht (depthWord t _) h'k he Y hY -- fix

lemma full : OnPath U C := by
    refine ⟨⟨p.arc,(fun i=>(p.panels i 0).huge),fun h' hs d N R hN hR F World h hOrder hPoint ε he=>?_⟩⟩
    by_contra! hδ
    obtain ⟨f,hf,hF⟩:= extraction_of_frequently_atTop hδ
    obtain ⟨c,Y,k,hk⟩ := podium_seq _ hp hg hk hm hC hE hS F R hR hs h' d f hf.tendsto_atTop (fun i=>(hF i).1)
    let V(i) := wok C d (f (i+k)) (p.arc d) c (Y i)
    have hP:=Next.UVStress.supply_wheel V hk hOrder h.smooth hC hPoint hs hR ε he
    obtain ⟨i,hi⟩:=hP.exists
    refine (hF (i+k)).2 ?_
    obtain ⟨U,hU,hA,H⟩:= Next.UVStress.harvested h hOrder h' (V i).toStation hi
    exact ⟨U,hU,hA,fun n ht=>H n (ht.trans hN)⟩
end YM.Pert.Dense
