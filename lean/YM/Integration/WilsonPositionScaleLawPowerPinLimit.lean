import YM.Integration.WilsonViewerAlignedPublic
set_option autoImplicit false
set_option warningAsError true
noncomputable section
universe u
namespace YM.Integration.WilsonPositionScaleLawPowerPinLimit
open WilsonViewerElectedHierarchy
open Function Filter Set MeasureTheory Spec Extraction Table PhysicalNext.Repeat.Legato Lattice
open OPE OPE.Orbits OPE.Orbits.Reader Climb RG17 PhysMS Trace.Pilot
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale MS MS.Land MS.Fleet
open WilsonThermometerWeakMeasuredSeries WilsonPositionHomogeneousFrame
open WilsonViewerGridPins WilsonViewerReportingGrid WilsonViewerAlignedResidual
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    {F:Final R.family f S} {Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J:ℝ→PhysMS.tower S} {L:EveryPhase.Almanac F} {Y:(Bel R.family.book).Hierarchy}
    {arch:Trace.Terrace.Arch R.family} {ℓ:Ultrafilter (ℕ×ℕ)} {simple:G.Simple}
    {cohort:Ultrafilter (ℕ×ℕ)→Prop} (run:Selected.{u} F L Q J Y arch ℓ simple cohort)

variable (Z:WilsonPrescription G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)} {branch:Bool} (ms:Main.Match Z simple M σ branch)
    (ν:ℝ) {n H:ℕ} {d:Caps n} (v:MaxwellSlots R.family d) (within:∀i,d i≤H)
local notation "pub" => homogeneous F J Z
local notation "θ" => reading F J Z
local notation "c" => coefficient Z M ν H (commonCaps v within)

private theorem triangle (left mid right:ℂ):‖left-right‖≤‖left-mid‖+‖mid-right‖:=by
  simpa only [dist_eq_norm] using dist_triangle left mid right

theorem exchange {order:Extraction.Order}{row:ℕ→ℕ→ℂ}{u:ℕ→ℂ}{x:ℂ}{B ε:ℝ}
    (positive:0<ε)(limit:Tendsto u atTop (𝓝 x)):
    ((∃ᶠ i:ℕ in atTop,order.late fun N per=>‖row N per-u i‖≤B)→
      order.late fun N per=>‖row N per-x‖≤B+ε) ∧
    ((order.late fun N per=>‖row N per-x‖≤B)→
      ∀ᶠ i:ℕ in atTop,order.late fun N per=>‖row N per-u i‖≤B+ε):=by
  have near:∀ᶠi in atTop,‖u i-x‖<ε:=
    (tendsto_iff_norm_sub_tendsto_zero.mp limit).eventually (gt_mem_nhds positive)
  constructor
  · intro reads
    obtain ⟨i,old,small⟩:=(reads.and_eventually near).exists
    unfold Extraction.Order.late at old ⊢
    exact old.mono fun per h=>h.mono fun k yes=>
      (triangle (row (order.mesh k) (order.per per)) (u i) x).trans (add_le_add yes small.le)
  · intro reads
    filter_upwards [near] with i small
    have back:‖x-u i‖≤ε:=by rw [norm_sub_rev];exact small.le
    unfold Extraction.Order.late at reads ⊢
    exact reads.mono fun per h=>h.mono fun k yes=>
      (triangle (row (order.mesh k) (order.per per)) x (u i)).trans (add_le_add yes back)

def cut (P:Report F ℓ H θ)(r:ℝ)(o:Fin n → Cover)(N per:ℕ):ℂ:=
  atCut (R:=R) d (P.grid.date r) o
    (fun u i=>(P.rows r).field ⟨d i,Nat.lt_succ_of_le (within i)⟩ u (pub r (d i) (v i))) (N,per)

def Price (P:Report F ℓ H θ)(W:Finset E4)(p q:ℕ):Prop:=
  ∀K,IsCompact K→K⊆conf n→∃C,0≤C ∧ ∀ᶠr in trail,∀o y,y∈K→
    Pin R.family.S W r (P.grid.date r) o y→
    f.late fun N per=>‖cut Z v within P r o N per-approximate c q (θ r) y‖≤C*(θ r)^p

theorem original (P:Report F ℓ H θ)(W:Finset E4)(p q:ℕ)(live:∀ᶠr in trail,0<θ r):
    PinBill Z M ms ν v within P W p q ↔ Price Z M ν v within P W p q:=by
  constructor
  · intro signed K compact clear
    obtain ⟨C,nonneg,fee⟩:=signed K compact clear
    refine ⟨C+1,by linarith,?_⟩
    filter_upwards [fee,live] with r hr pos
    intro o y hy pin
    have trade:=exchange (order:=f) (row:=cut Z v within P r o) (B:=C*(θ r)^p) (pow_pos pos p)
      (WilsonViewerGridMS.point Z M ms ν (commonCaps v within) q (θ r) y (clear hy))
    simpa only [cut,add_mul,one_mul] using trade.1 (hr o y hy pin)
  · intro signed K compact clear
    obtain ⟨C,nonneg,fee⟩:=signed K compact clear
    refine ⟨C+1,by linarith,?_⟩
    filter_upwards [fee,live] with r hr pos
    intro o y hy pin
    have trade:=exchange (order:=f) (row:=cut Z v within P r o) (B:=C*(θ r)^p) (pow_pos pos p)
      (WilsonViewerGridMS.point Z M ms ν (commonCaps v within) q (θ r) y (clear hy))
    simpa only [cut,add_mul,one_mul] using (trade.2 (hr o y hy pin)).frequently

end YM.Integration.WilsonPositionScaleLawPowerPinLimit
end
