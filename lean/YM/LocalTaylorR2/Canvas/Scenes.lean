import YM.Pressure.Route
import YM.LocalTaylorR2.Mesh.Flat

/-!
# Seasonal field-gauge. Canonical symmetric *within* the given channel-axis.

Keeps roots even if another partner uses another chart. Conjugation gauge
covariant on *all* fields -- not equating measured formula with its exterior
use. Rt price needed later for Taylor logarithm. Estimate even when Room would
fail to pay the full hull of paths capped only by LENGTH (voltage jets will
need ≥ 24B). Use actual axis-box aperture. Cost slack after L.

The argument uses lease flattening from Work.E08 and the Pressure step telescoping estimate for walks.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Canvas
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {D : ℕ} {o : Site c} {V : Config G c} {s p : ℝ}
open Axial Channel
lemma billboard (p : List Axis) (h:p.Nodup)(r : ℕ) (U: CoverConfig G) (x y: Pressure.Place r) (q:ℝ)(hp:0≤q)
    (he : ∀ v : Cover,v∈box r→ ∀ i:Axis, G.chord (U (v,i)) ≤ q) : G.chord (travel U x.val (axisRoute x.val y.val p)) ≤ (p.length:ℝ)*(2*r+1)*q:=by
  induction p using List.reverseRecOn with
  | nil => simp [axisRoute,travel]
  | append_singleton p j ih=>
    rw [List.nodup_append] at h
    have hj:j∉p := fun hh=> h.2.2 j hh j (by simp) rfl
    let z:= discord r p x y; have hz : z.val j=x.val j:= if_neg hj
    have hh : stop x.val (axisRoute x.val y.val p)=z.val:= by
      rw [axisRoute_end x.val y.val x.val p h.1]; funext i; simp only [z,discord]; split <;> rename_i h <;> simp
    have hk := Pressure.step_cost r j U z (⟨y.val j,(box_iff_layers ..).1 y.property j⟩: Pressure.Height r); rw [hz] at hk
    rw [axisRoute_append,travel_append,hh]; apply (G.chord_triangle ..).trans
    apply le_trans (b:=(p.length:ℝ)*(2*r+1)*q+(∑ _ :Pressure.Height r,q))
    · refine add_le_add (ih h.1) ?_; simp only [axisRoute,List.flatMap_singleton]; apply hk.trans
      refine sum_le_sum fun w hw=>?_; unfold perEdge; split
      next hf=>exact he _ (Pressure.slide ..).property _
      next =>exact hp
    simp [Pressure.Height,card_layers]; apply le_of_eq; ring

lemma riding (r : ℕ) (x : Site c)(hx:separation o x≤r)(hp:0≤p)(he : ∀ i : Bond c,separation o i.1≤r→ G.chord (V i)≤p):
    G.chord (carrier o V x)≤ 4*(2*(r:ℝ)+1)*p:=by
  have h:= billboard (allAxes 1) ((List.nodup_finRange _).map (1:Lattice.Order).injective) r (expandAt o V)
    ⟨0,center_box _⟩ ⟨Lattice.lift (x-o), Work.E08.lift_mem_box hx⟩ _ hp (fun v hv i=> he _ (Work.E08.separation_box_add o hv))
  rw [travel_at] at h; rw [show (allAxes 1).length=4 from by simp [allAxes],map_zero,zero_add] at h
  exact_mod_cast h

def pedestal (x:Site c) (V:Config G c): Config G c:= Lattice.gauge (carrier x V) V
lemma around (z: Site c→G.El) (o : Site c) (V: Config G c) : pedestal o (Lattice.gauge z V)=Lattice.gauge (fun _=>z o) (pedestal o V):=by
  ext1 i; unfold pedestal
  rw [Lattice.gauge]; simp_rw [carrier,travel_gauge,deposits]
  unfold Lattice.gauge carrier; group
lemma next_le {o : Site n} {i:Bond n} {r:ℕ}(h:separation o i.1≤r): separation o (i.1+step i.2)≤r+1:= (separation_triangle o i.1 _).trans (Nat.add_le_add h (Work.E01.sep_step_le ..))

def reserve (r:ℕ):ℝ:= (2*(4*(2*(r:ℝ)+1))+1)*(16*(2*((r+1:ℕ):ℝ)+1)^5*(Fintype.card PlaqAxes:ℝ))
lemma draw {q:ℝ} (r : ℕ) (i:Bond c)(hs:2*(r+1)<c.val) (hv : separation o i.1 + 1≤ r) (ht:Clean V s o (r+1)) (hp : 0≤ q)(he: Pressure.temp s ≤ q): G.chord (pedestal o V i)≤ reserve r * q:=by
  obtain ⟨z,hz⟩:= Work.E08.axial_patch o V r (r+1) le_rfl hs q hp (fun y ht' p=> (ht.toll (b:=(y,p)) ht').trans he)
  let B:=16*(2*((r+1:ℕ):ℝ)+1)^5*(Fintype.card PlaqAxes:ℝ)*q; let K:= 4*(2*(r:ℝ)+1)*B; let W:=Lattice.gauge z V
  have hl v (h:separation o v ≤ r): G.chord (carrier o W v) ≤ K:= riding _ v h (p:=B) (by unfold B; positivity) hz
  let y:= i.1 + step i.2; have hV : G.chord (carrier o W y) ≤ K:= hl y ((next_le (r:=separation o i.1) le_rfl).trans hv)
  have ht : G.chord (pedestal o W i) ≤ reserve r*q:=by
    apply (G.chord_triangle ..).trans; -- unfold pedestal before rw
    rw [Gauge.chord_inv]
    apply (add_le_add ((G.chord_triangle ..).trans (add_le_add (hl i.1 (by omega)) (hz i (by omega)))) hV).trans_eq; unfold reserve K B; ring
  unfold W at ht; rw [around,Lattice.gauge,G.chord_conj] at ht; exact ht

-- Stencil comparison and jets use coarser locality via length. They needn't preserve analytic Room along support (pricing draws with `Clean` at center).
lemma admits {D r : ℕ} {V U:Config G c} (h:AgreeNear id o D V U) (he : 4*(r+1) ≤ D) : AgreeNear id o r (pedestal o V) (pedestal o U):=by
  have hm (i: Site c)(hp:separation o i≤ r+1): carrier o V i=carrier o U i:= carrier_near o i V U D h (by omega)
  intro j hj; change separation o j.1≤ r at hj; rw [pedestal,Lattice.gauge, hm j.1 (by omega), hm (j.1+step j.2) (next_le hj),h j (by simp only [id_eq]; omega)]; rfl
end YM.LocalTaylorR2.Canvas
