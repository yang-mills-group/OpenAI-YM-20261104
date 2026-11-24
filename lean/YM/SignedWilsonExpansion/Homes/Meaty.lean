import YM.SignedWilsonExpansion.Homes.LimitG

/-! Full ordered limit precision of the N MICRO, on its companion track. Paired estimates. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.SignedWilsonExpansion.Homes
open Function Filter Set MeasureTheory Extraction Climb Spec Table Next.UVStress OPE.Levy Trace.Pilot PhysMS PhysMS.Frame
open MergeProof.East Next.Rank Ward Next.Rank.East Pert.Scale Maxwell Extra.FD PhysicalNext.Repeat.Legato Run Lattice FullVolume Cells BeamT
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} (R:Run G)(h:G.Simple) {f:Extraction.Order} {S:Table R.family.book} (F:Final R.family f S)
   {n:ℕ} {ι:Type*} {L:Filter ι}
   (trackP:(track f).Ordered R.family S) (trackV:(track f).PointLimits R.family S) (H:(Bel R.family.book).Hierarchy)
   {r:ι→ℝ} (hr:Tendsto r L trail) {J:ℝ→tower S} (P:Leading F J)
local notation "R₀" => R.family
include F H trackV trackP P h hr

lemma projectionP (d:Caps n){ℓ:ι→ℝ} (hℓ:pivotT L r ℓ) {B:ι→BeamT R.family} (hp:Tendsto (fun i=>(B i).k) L atTop) (hx:∀ᶠ i in L, (B i).Given (track f) H (ℓ i))
   (k:ι→ℕ)(z:ι→Fin n→ Cover){v:ι→Points n} (γ:∀ᶠ i in L,r i • v i=Order.grid R.family (k i) (z i)) {y:Points n} (hy:y∈ conf n) (hV:Tendsto v L (𝓝 y)) {w:ι→MaxwellSlots R.family d} {Y:MaxwellSlots R.family d} (hc:∀ j,Tendsto (fun i=>w i j) L (𝓝 (Y j))) :
   Tendsto (fun i:ι× (ℕ×ℕ)=> MICRO R.family i.2 (k i.1) (z i.1) d (fun _=>B i.1) (r i.1) (fun _=>ℓ i.1) (w i.1)) (L.curry (track f).fuse) (𝓝 (WickGoal Y y)) := by
   apply pairsC (f:=(track f).fuse) (L:=L) (X:=fun i u=> MICRO R.family u (k i) (z i) d (fun _=>B i) (r i) (fun _=>ℓ i) (w i)); intro U hU
   obtain ⟨p,pH⟩:= chooseV (L:=L) (hx.mono fun i hi=> (B i).housed F.room.kernel trackP H R.makes (U i) (hU i) hi)
   refine ⟨fun i=> shelter (r i) (fun _=>ℓ i) (fun _=>p i) (w i) (v i),?_,?_⟩
   · filter_upwards [pH,eventually_all.mpr (fun j=> hp.eventually_ge_atTop (d j)),γ,hr.eventually self_mem_nhdsWithin,hV.eventually ((conf_open n).mem_nhds hy)] with i H' card p' hr hv
     exact considered R h F.room.kernel trackV _ _ _ p' (Work.A05.smul_conf hr hv) _ card _ (U i) (hU i) fun _=> H'.1
   exact pivotW P hr hℓ hp (pH.mono fun i hi=>hi.2) hy hV d hc

lemma projectionM {n:ℕ} (d:Caps (n+1)){ℓ:ι→Fin (n+1)→ℝ} (hℓ:∀ j,pivotT L r (fun i=>ℓ i j)) {B:ι→Fin (n+1)→BeamT R.family} (hp:∀ j,Tendsto (fun i=>(B i j).k) L atTop) (hx:∀ᶠ i in L,∀ j, (B i j).Given (track f) H (ℓ i j))
   (k:ι→ℕ)(z:ι→Fin (n+1)→ Cover){v:ι→Points (n+1)} (γ:∀ᶠ i in L,r i • v i=Order.grid R.family (k i) (z i))
   {K:Set (Points (n+1))} (hK:IsCompact K) (hy:K⊆ conf (n+1)) (hV:∀ᶠ i in L, v i∈ K) {w:ι→MaxwellSlots R.family d} {Y:MaxwellSlots R.family d} (hc:∀ j,Tendsto (fun i=>w i j) L (𝓝 (Y j))) :
   ∃ ε:ℝ, ∀ᶠ (i:ι× (ℕ×ℕ)) in L.curry (track f).fuse, ‖MICRO R.family i.2 (k i.1) (z i.1) d (B i.1) (r i.1) (ℓ i.1) (w i.1)‖ ≤ ε := by
   refine pairCostC (L:=L) (X:=fun i u=> MICRO R.family u (k i) (z i) d (B i) (r i) (ℓ i) (w i)) (f:=(track f).fuse) (hp 0) ?_; intro U hU
   choose p hP using fun j:Fin (n+1) => chooseV (L:=L) (hx.mono fun i hi=> (B i j).housed F.room.kernel trackP H R.makes (U i) (hU i) (hi j))
   refine ⟨fun i=> shelter (r i) (ℓ i) (fun j=>p j i) (w i) (v i),?_, mixed P hr hℓ hp ((eventually_all.mpr hP).mono fun i hi j=>(hi j).2) hK hy hV d hc⟩
   filter_upwards [eventually_all.mpr hP,eventually_all.mpr (fun j=> (hp j).eventually_ge_atTop (d j)),γ,hr.eventually self_mem_nhdsWithin,hV] with i H' card p' hr hv
   exact considered R h F.room.kernel trackV _ _ _ p' (Work.A05.smul_conf hr (hy hv)) _ card _ (U i) (hU i) fun j=> (H' j).1

end YM.SignedWilsonExpansion.Homes
