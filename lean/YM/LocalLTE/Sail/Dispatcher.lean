import YM.LocalLTE.Sail.Permit
/-! Steering physical aperture keys. Queries don't assume receipts beyond availability.Special geometry all passports. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Sail
open Set Function Filter MeasureTheory Lattice RG Wilson Extra.Histories
open MergeProof Menu Marker Accent XPhase Overlay PhysicalNext.Repeat Next.Foundations Planned.GuardedAtom Guard
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge} {n : Side}{V:Type} [DecidableEq V][Fintype V]
structure Batch (P:History G)(N p:ℕ)(Z:Type) where
    demand: Z→ℕ
    voice: ∀ i,((Labels.frames G).level (demand i)).Coeff
    motion: Z→Extra.Histories.Motion
    origin: (j:ℕ)→Z→Site (P.S.side j p)
variable {N p:ℕ} {P:History G} (b:Batch P N p V) (B:Census V)
    (A:∀ d,Extra.Histories.Music ((Labels.frames G).level d) P N p)
variable (i:ℕ)
-- compare at exactly the stage address. Output goes to these supports.
namespace Batch
abbrev steering (j:ℕ):= ∀ v,(P.rep N p j).activities.Moves (b.motion v).1 (b.origin j v)
abbrev label (v:V):= A (b.demand v)
def requested (j:ℕ)(v:V):Config G (P.S.side j p)→ℂ:= Sail.glyphSeed P N p (b.voice v) (b.motion v) (fun j=> b.origin j v) (b.label A v) j
variable {j:ℕ} (k:b.steering j)
noncomputable abbrev named (v:V) : Source.Coefficient ((Labels.frames G).level (b.demand v)) (P.S.side j p) := Sail.imprint P N p (b.voice v) (b.motion v) (fun i=> b.origin i v) (b.label A v) (k v)
noncomputable def wavelengths (v:V) := primProbe P N p (b.voice v) (b.motion v) (fun i=>b.origin i v)
noncomputable abbrev raw := Accent.birth B (P.rep N p N) b.wavelengths
structure Wants (m:ℕ)(r₀:ℕ→ℕ)(K:ℕ) : Prop where
    registered v : r₀ (b.demand v) ≤ m
    lines: Fintype.card V ≤ K
    taps i v : m ≤ i → i<N → b.origin (i+1) v = (P.levels.clock.op i p).ratio.embed (b.origin i v)
    marks v: ((Labels.frames G).level (b.demand v)).coeffSize (b.voice v)≤1
variable {m K:ℕ}{r₀:ℕ→ℕ}{W:Bid.Worth}
structure Roles (m:ℕ)(W:Bid.Worth)(r₀:ℕ→ℕ)(K:ℕ):Prop where
    phase : Wants b m r₀ K
    text : ∀ i, Sung (localSection G (b.demand i)) P N p (hol G) W (r₀ (b.demand i)) (b.label A i)
variable (h : Roles b A m W r₀ K)
include h
local notation "q'"=> b.label A
local notation "K'"=> P.rep N p j
omit h [Fintype V] [DecidableEq V] in
lemma labels_equal (v:V): requested b A j v=(named b A k v).exponentialEntry (b.origin j v) (localSection G (b.demand v)) K':=by
   apply sunny_ray .. -- order?
-- Actually h,hv,ht unused here; derive Sight.Frame in parallel
omit [DecidableEq V] in
lemma financed (hv:m≤ j)(ht:j≤N)(v:V) : (named b A k v).Format (b.origin j v) (hol G) (P.rep N p j) ∧ Dominated (named b A k v).forced:=by
    obtain ⟨-,hE,hh⟩:= Sail.stamp_signal P N p (b.voice v) (b.motion v) (fun i=> b.origin i v) (b.label A v) (k v) ((h.text v).earned j ((h.phase.registered v).trans hv) ht); exact ⟨hh,hE⟩
omit [DecidableEq V] in
lemma transfers (k':b.steering (j+1))(hp:P.Selected) (hv:m≤ j)(ht:j<N)(v:V): Accent.coin (P.rep N p j) (requested b A j v) (named b A k v).forced=(P.levels.clock.op j p).push (P.rep N p (j+1)).beta (Accent.coin (P.rep N p (j+1)) (requested b A (j+1) v) (named b A k' v).forced):=by
    let f:= b.label A v; have he:=(h.phase.registered v).trans hv
    exact fromStep P N p (b.voice v) (b.motion v) (fun i=> b.origin i v) (b.label A v) (k v) ((h.text v).earned j he ht.le) hp (k' v) ht ((h.text v).earned (j+1) (by omega) ht) ((h.text v).step j he ht) (h.phase.taps j v hv ht)
end Batch
end YM.LocalLTE.Sail
