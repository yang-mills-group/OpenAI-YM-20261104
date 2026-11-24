import YM.Comparison.RG02.Symphony.Harness
/-! Accept any cover-based symbols from formal prescription if they mirror FFTs of
 moving-v local coefficient library (INCLUDING all the same input higher Γ), analytic
 at k=0. Prove low identity from actual `Chain` with stationary horizon, needs Swears. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Symphony
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested
open Marker Multi Order YM.Next.SectorChange Laplace Symmetry Symmetry.Orbit
open Moving Moving.Path Moving.Shift Valence Adjacent Assembly LocalScript
open Matrix Push.Loops Laurent Bloch YM.Work.F05
open YM.AnalyticNext.QuarticMatch.Joint (shifts)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.L2Operator
variable {G:Gauge} {P : RG.History G}
variable (L:Bulk.Chain P) (N m r:ℕ) (h:m<N) (k i:ℕ)
set_option quotPrecheck false
local notation "P₀"=> L.horizon.H N m
local notation "ν"=> Project P m
local notation "α"=> L.kin.alpha N m
local notation "Q"=> L.kin.path N m
local notation "S" i=> (P.levels.clock.op m i)
local notation "J"=> Seed.second P₀ Q α
local notation "K"=> kineticSymbol G ((L.horizon.H N m).metric)
variable (hp:star (0:Momentum)=0) -- for simpl probes
namespace Roster
variable {Z:MapPrices}
include h
variable (H:L.horizon.Suffices Z)(HE:∀i, Bid.Sworn (L.horizon.H N m) (P.S.side m i) G)
variable (q:Momentum) (he:star q=q)
include he H
lemma real_kernel : ContDiffAt ℂ ω (kineticSymbol G ((L.horizon.H N m).metric)) q:= kinetic_diff (H.rows N m h.le).2.1 (Z.alpha_pos _) (Work.F07.realStrip _ (half_pos (Z.alpha_pos _)) he)
omit H in
lemma real_loop : ContDiffAt ℂ ω (loopSymbol (L.kin.path N m)) q:= by have hp:= L.planned.cap N m h.le; exact loop_diffAt hp.width (loopRow_budget hp.width hp.two) (Work.F07.realStrip _ (half_pos hp.width) he)
lemma real_quad : ContDiffAt ℂ ω (Seed.second P₀ Q α) q:= ((real_kernel L N m h H q he).const_smul (α:ℂ)).add (real_loop L N m h q he)
omit he
variable (a:G.ColorIndex)
theorem pays : probe₂ (kineticSymbol G ((L.horizon.H N m).metric)) a=1:= kinetic_probe (row_analytic (H.rows N m h.le).2.1 (Z.alpha_pos _) (Work.F07.realStrip _ (half_pos (Z.alpha_pos _)) (star_zero (R:=Momentum)))) (H.all N m h.le (Project P m 0)).starts a
theorem keeps: probe₂ (Seed.second (L.horizon.H N m) Q α) a=(α:ℂ):= by
   unfold Seed.second; rw [probe_add a (V:= (α:ℂ) • K) ((real_kernel L N m h H 0 (star_zero ..)).const_smul (α:ℂ)) (real_loop L N m h 0 (star_zero ..)), probe_smul,pays L N m h H,mul_one]; have hp : probe₂ (loopSymbol Q) a=0:= div_eq_zero_iff.mpr (Or.inl (loop_four (L.planned.cap N m h.le) (unitAxis 0) (1,a) (1,a) 2 (by decide))); rw [hp,add_zero]

variable {V:Type}[Fintype V][DecidableEq V] {R:Census V}
    (F: ∀ i,Forest (P.levels.clock.op m i).ratio) (u:∀ i,(P.levels.clock.op m i).Choices)(W: ∀ i,Bulk.Colors R G (P.S.side (m+1) i))
    (hr:2≤r)(hW:∀ i,(W i).Standard)
local notation "Γ"=> (fun i:ℕ=> ground (L.step N m i h) (F i) (u i) (W i) r)
def series : Columns G (Project P m):= fun k i=> ground (L.step N m i h) (F i) (u i) (W i) r k
local notation "Ξ"=> series L N m r h F u W
include HE
lemma zeroth : Offer K (series L N m r h F u W 0):= by
   have hh := Z.alpha_pos (P.levels.clock.J m)
   refine ⟨real_kernel L N m h H _ (star_zero ..),?_⟩; apply Breeze.referral (b:=fun _=>0) _ tendsto_const_nhds fun q he=> (real_kernel L N m h H q he).continuousAt
   intro i; rw [series,Seed.reserveO L N m r i h _ _ _ H (HE i)]; exact Breeze.accepts_zero _ (Compares.of_routed (b:=Axes G) fun _ _ hp=>kinetic_routed G _ (Row.rights _ _ (H.rows N m h.le).2.1 hh.le) hp)
include hr hW
omit H HE in
lemma first (hG:G.Simple): Offer (0:SpecK G) (series L N m r h F u W 1):= Offer.none fun i=> Seed.no_k L N m r i h _ _ _ hr (hW i) hG
lemma second : Offer (Seed.second (L.horizon.H N m) Q α) (Ξ 2):= by
   refine ⟨real_quad L N m h H _ (star_zero ..),?_⟩; exact (Breeze.referral (b:=Seed.issue P L m) (fun i=> Seed.deviation L N m r i h (F i) (u i) (W i) hr (hW i) H (HE i)) (Seed.season L m) (fun q he=> (real_quad L N m h H q he).continuousAt))
def core : ℕ→ SpecK G | 0=>K | 1=>0 | 2=> J | _=> 0
-- Canon uses cofinal Offer. For few low grades here actually provide all Offers. Signature above consumes spin (with Body); Calm for even continuation optional.
variable (hG:G.Simple)
include hG
theorem supply (hr':k≤2) : Offer (core L N m k) (series L N m r h F u W k):= by
    interval_cases k
    · exact zeroth L N m r h H HE F u W
    · exact first L N m r h F u W hr hW hG
    exact second L N m r h H HE F u W hr hW
end Roster
end YM.Comparison.RG02.Symphony
