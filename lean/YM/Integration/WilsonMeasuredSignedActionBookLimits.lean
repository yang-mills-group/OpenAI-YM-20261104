import YM.Integration.WilsonMeasuredSignedActionReserve
import YM.Integration.WilsonMeasuredSignedActionRegistry

/-! The Ward sign holds for every zoom of the funded physical books. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionBookLimits
open Function Filter Set Finset Extraction Table Spec Climb Maxwell Maxwell.Free Lattice RG Wilson
open Trace Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph Source Labels
open Trace.Over Trace.Terrace Trace.Pilot TraceExtension MergeProof.East Next.Rank Next.UVStress
open PhysicalNext.Repeat.Legato Further.CorrectedLift
open WilsonMeasuredPublicEntranceGridDebit WilsonOriginalTwoFlatPublicBooks
open WilsonPositionThermometerCapStation WilsonOriginalThermometerPalette
open WilsonMeasuredSignedActionCourse WilsonMeasuredSignedActionAverage
open WilsonOriginalMicroscopicGuardedReporters MergeProof Campaign
open WilsonMovingForkHeterogeneousCut (Filed)
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {H:(Bel R.family.book).Hierarchy}{l:Ultrafilter (ℕ×ℕ)}{Z:Arch R.family}
    {T:Campaign R}(L:Pillars R T)
local notation "C" => R.family
local notation "F₀" => R.family.labels.level 4


open WilsonMeasuredSignedActionRegistry (weak HeardAt)

theorem extract {cap:ℕ→ℕ}{test:ℕ→Prop}(grows:Tendsto cap atTop atTop)
    (sale:∀φ:ℕ→ℕ,StrictMono φ→(∀m,m≤cap (φ m))→∀ᶠm in atTop,test (φ m)):
    ∀ᶠm in atTop,test m:=by
  by_contra! bad
  obtain ⟨φ,rises,misses⟩:=extraction_of_frequently_atTop bad
  have room(q:ℕ):∃c,∀m≥c,q≤cap (φ m):=
    eventually_atTop.1 ((grows.comp rises.tendsto_atTop).eventually_ge_atTop q)
  choose cut afterCut using room
  let stage(n:ℕ):=n+(Finset.range (n+1)).sup cut
  have moves:StrictMono stage:=by
    apply strictMono_nat_of_lt_succ
    intro n
    have comp:(Finset.range (n+1)).sup cut≤(Finset.range (n+1+1)).sup cut:=
      Finset.sup_mono (Finset.range_mono (Nat.le_succ _))
    dsimp only [stage]
    omega
  have large(m:ℕ):m≤cap (φ (stage m)):=by
    apply afterCut m (stage m)
    have enough:cut m≤(Finset.range (m+1)).sup cut:=Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self _))
    dsimp only [stage]
    omega
  obtain ⟨m,hm⟩:=(sale (φ ∘ stage) (rises.comp moves) large).exists
  exact misses (stage m) hm

include L in
theorem original (simple:G.Simple)(bliss:Bliss F l Z H)
    {J:ℝ→PhysMS.tower S}{P:ℝ→Spin.change S 4}{δ g:ℝ→ℝ}
    (frame:∀ᶠ r in trail,J r 4=P r)(cal:TendC F P δ)(heat:Coupling G g)
    (X:Zoom){D T:ℕ→ℕ}(B:∀m,Book F (l:=l) H Z (D m) (T m) (X.r m))
    (roof:Tendsto (fun m=>(B m).k) atTop atTop)(stages:Tendsto (fun m=>(B m).W.k) atTop atTop):
    ∀ᶠ m:ℕ in atTop,∀ i:4≤D m,∀ᶠ z:ℕ×ℕ in f.fuse,
      HeardAt R (B m).W.k z.1 z.2 (weak R F (B m) i (J (X.r m)) z):=by
  apply extract roof
  intro φ up raises
  let Y:Zoom:=⟨X.r∘φ,fun n=>X.positive (φ n),X.shrinking.comp_strictMono up,X.limits.comp up.tendsto_atTop⟩
  exact WilsonMeasuredSignedActionRegistry.original R F L simple bliss frame cal heat Y (fun m=>B (φ m)) raises
    (stages.comp up.tendsto_atTop)

theorem scheduled {D t:ℕ}{ρ:ℝ}(B:(s:{s:ℝ // 0<s ∧ s<ρ})→Book F (l:=l) H Z D t s.val)
    (grows:∀k:ℕ,∀ᶠr in trail,∀p:0<r,∀h:r<ρ,k≤(B ⟨r,p,h⟩).k ∧ k≤(B ⟨r,p,h⟩).W.k)
    (X:Zoom)(inside:∀m,X.r m<ρ):
    let b:=fun m=>B ⟨X.r m,X.positive m,inside m⟩
    Tendsto (fun m=>(b m).k) atTop atTop ∧ Tendsto (fun m=>(b m).W.k) atTop atTop:=by
  have under:Tendsto X.r atTop trail:=tendsto_nhdsWithin_iff.mpr ⟨X.limits,Eventually.of_forall X.positive⟩
  constructor
  · apply tendsto_atTop.mpr
    intro k
    exact (under.eventually (grows k)).mono (fun m seen=>(seen (X.positive m) (inside m)).1)
  · apply tendsto_atTop.mpr
    intro k
    exact (under.eventually (grows k)).mono (fun m seen=>(seen (X.positive m) (inside m)).2)

end YM.Integration.WilsonMeasuredSignedActionBookLimits
end
