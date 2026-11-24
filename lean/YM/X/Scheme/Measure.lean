import YM.X.Scheme.Rung
import YM.X.Scheme.Slide
/-!
Exact local solve and formal-prolongated solves of independent diagram arrays. No uniformity of mesh in d needed; convergence to remove coupling regulator still separate. Stabilizer removed square, equality even at order zero, inversion-odd orientation ever after.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Detector
open Function Filter Set Pert Pert.Position Jet
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {F:Labels.Frames G} {d e n:ℕ}
variable (D:Detector F d)
local notation "M"=> Bank F d
local notation "L"=> Buffer F d
local notation "A"=> pureBank F d

variable {v:Buffer F d} {w:Word (Bank F d)} {b:Word (Buffer F d)}

def announce (D: Detector F d) (w:Word (Bank F d)) (b:Word (Buffer F d)) := D.D ∘ predMarket b w = just (D.D (pureBank F d))
def report (D:Detector F d) (w:Word (Bank F d)): Word (Buffer F d) := run (pick D.slips) (D.read ∘ w)
lemma readOut {v:ℝ→Bank F d}(ha:Appears n v w):Act n (D.read ∘ v) (D.read ∘ w):= Act.all_picks fun i=> ha.discolor (Rail.reachedV D.rail i).f
lemma announce_labels : D.D ∘ predMarket b w = run D.rail.tableMap (Jet.pair (D.read ∘ w) b) := by
    funext k; let q:= delay w k; let v:=delay b k
    have he:= appears_delay w k; have hk: Act k v b:= Act.swell b le_rfl
    have hm:= (appears_market he hk).collect (X:=Buffer F d) (by exact D.finiteD)
    let f (t:ℝ) := D.D (market F (v t) (q t))
    have hf : f=(D.rail.tableMap ∘ (fun t=>(D.read (q t),v t))) := funext fun t=>Eq.symm (D.chartD ..)
    exact Act.trans_at (show Act k f _ from hm) (hf.symm ▸ (((D.readOut he).zipper hk).transit D.rail.tableMap_smooth.contDiffAt)) le_rfl

def patch (D:Detector F d) (v: Bank F d) : Prop:= Region D.slips D.rail.tableMap D.parameter (D.read v) (D.slips (D.read v,0))
def solve0 (v:Bank F d): Buffer F d:= D.slips (D.read v,0)
@[simp] lemma report_zero (w:Word M) : D.report w 0=D.solve0 (w 0):= (run_zero ..)
lemma patch_solves {v : Bank F d} (h:D.patch v): D.D (market F (D.solve0 v) v)=D.D A:= by
   rw [← chartD]; exact h.match_.trans D.chart_unit
lemma patch_announces (h : D.patch (w 0)): D.announce w (D.report w):= by
   unfold Detector.announce; rw [announce_labels,report]; rw [Jet.region_writes _ (u:=D.solve0 (w 0)) (by exact h) D.rail.tableMap_smooth, D.chart_unit]
lemma patch_only (h:D.patch (w 0))(hb:b 0=D.solve0 (w 0))(ha:D.announce w b): b=D.report w:= by
   funext k; refine uniqueness (n:=k) (a:=D.read ∘ w) (show Region .. from h) D.rail.tableMap_smooth b hb ?_ k le_rfl
   unfold announce at ha; rw [← announce_labels,ha,D.chart_unit]; exact (Jet.Act.static (n:=k) _).writes

-- generic convergent input array per test (e.g. Shop). Local branch unique even if read basis chosen nonunique. All horizon-wise shrink.
variable {X:Type*} {l: Filter X}{q:X→ Bank F d}
variable (h:∀ s:Section F d,Tendsto (fun x=>lookie F s (q x)) l (𝓝 (lookie F s (pureBank F d))))
lemma slip_region : ∀ᶠ v in 𝓝 D.parameter,Region D.slips D.rail.tableMap D.parameter v (D.slips (v,0)):= Jet.around D.slip_spec
include h
lemma patches : ∀ᶠ x in l,D.patch (q x):= (D.rail.common_limit h).eventually D.slip_region
lemma appears_solve0 : Tendsto (fun x=> D.solve0 (q x)) l (𝓝 0):= by
   have hh:= D.slip_spec; rw [← hh.fixes]; exact hh.diff.continuousAt.tendsto.comp ((D.rail.common_limit h).prodMk_nhds tendsto_const_nhds)
lemma legal {v:X → Buffer F d}(hh:Tendsto v l (𝓝 0)): ∀ᶠ x in l,(D.D (market F (v x) (q x))= D.D A) ↔ D.solve0 (q x)=v x:= by
   filter_upwards [ (((D.rail.common_limit h).prodMk_nhds tendsto_const_nhds).prodMk_nhds hh).eventually D.slip_spec.strict] with x hx
   rw [← chartD, ← chart_unit D]; exact (by unfold solve0; unfold Jet.center at hx; simpa [Function.comp_def,Detector.read] using hx)
end YM.PositionX.Detector
