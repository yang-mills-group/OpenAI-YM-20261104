import YM.SignedWilsonExpansion.Homes.Flanker

/-! One installed scale factor. Every compact set and every fixed scheme mask
have common full-period bounds on the elected comparisons. Here first prove the same
at continuum partners associated to any ultrafilter below the elected full order. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.SignedWilsonExpansion.Homes
open Function Filter Set MeasureTheory Extraction Climb Spec Table Next.UVStress OPE.Levy Trace.Pilot PhysMS PhysMS.Frame
open MergeProof.East Next.Rank Ward Next.Rank.East
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book} {n:ℕ} {ι:Type*} {L:Filter ι}

lemma single {F:Final C f S}{J:ℝ→tower S}(H':Leading F J) {H:(Bel C.book).Hierarchy}{r:ι→ℝ} {D:ι→ℕ}{P:ι→Panel S} (hr:Tendsto r L trail)(hd:Tendsto D L atTop) (hs: ∀ᶠ i in L, HouseT F.room.kernel H (r i) (D i) (P i))
    {X:Set (Points n)}(hX:IsCompact X)(hx:X⊆conf n) (d:Caps n)(v:MaxwellSlots C d) :
     TendstoUniformlyOn (fun i => Coast (P i) (r i) v) (WickGoal v) L X:= by
   have E(U:Ultrafilter ι)(hu:(U:Filter ι)≤L): TendstoUniformlyOn (fun i => Coast (P i) (r i) v) (WickGoal v) (U:Filter ι) X := by
      let Z(i)(j:Fin n):= facN (P i) (J (r i)) (d j) (v j)
      have h(i:ι): Coast (P i) (r i) v = measured F none (J (r i)) (d:=d) (Z i) (r i) := by
         unfold Coast measured; simp_rw [Z,fac_value]; rfl
      choose K hK using fun j=> bounded_costT (d j) H' hr hd hs (v j)
      have pick(j): ∃ w, Tendsto (fun i=> Z i j) (U:Filter ι) (𝓝 w) := by
          obtain ⟨w,-,p⟩:= appointment (U:=U) (v:=fun i=>Z i j) (hZ:=isCompact_closedBall (0:(Bel C.book).Field (d j)) (K j)) ((hK j).filter_mono hu |>.mono fun i hi=> show Z i j ∈ Metric.closedBall _ _ by rw [Metric.mem_closedBall,dist_zero_right]; exact hi)
          exact ⟨w,p⟩
      choose w ψ using pick
      have W:= (coordU _ _).mpr (higher H' (hr.mono_left hu) (b:=0) ψ hX hx)
      simp_rw [← h] at W
      apply W.congr_right; apply Set.EqOn.mono hx
      apply (Test.unique_kernel (WickC _) (WickC _)).1
      intro t
      have q:= chargeV H' (hr.mono_left hu) ψ t; simp_rw [← h] at q; exact tendsto_nhds_unique q ((lateX hd hs d v t).mono_left hu)
   intro ε ep
   apply Filter.mem_iff_ultrafilter.mpr
   intro U hu; exact E U hu ε ep

-- moving signatures version
lemma vantage {F:Final C f S}{J:ℝ→tower S}(H':Leading F J) {H:(Bel C.book).Hierarchy}{r:ι→ℝ} {D:ι→ℕ}{P:ι→Panel S} (hr:Tendsto r L trail)(hd:Tendsto D L atTop) (hs: ∀ᶠ i in L, HouseT F.room.kernel H (r i) (D i) (P i))
    {X:Set (Points n)}(hX:IsCompact X)(hx:X⊆conf n) (d:Caps n){w:ι→MaxwellSlots C d}{v:MaxwellSlots C d} (hv:∀ j,Tendsto (fun i=>w i j) L (𝓝 (v j))):
     TendstoUniformlyOn (fun i => Coast (P i) (r i) (w i)) (WickGoal v) L X :=
   combinations (P:=fun x=>(Bel C.book).classMoment (Bel C.book) d x)
     (F:=fun i x=> (S.classMoment S d (r i • x)).compLinearMap (fun j=> P i (d j))) hX
     (fun _=> Module.finBasis ℂ _) (fun v=>(WickC v).mono hx) (fun w=>single H' hr hd hs hX hx d _) hv

lemma landArea {α:Type*} [TopologicalSpace α]{Y:Type*}[PseudoMetricSpace Y] {U:ι→α→Y} {V:α→Y}{x:ι→α} {y:α} {K:Set α}
   (hK:K∈ 𝓝 y)(h:TendstoUniformlyOn U V L K)(hr:Tendsto x L (𝓝 y)) (hp:ContinuousAt V y):
   Tendsto (fun i=> U i (x i)) L (𝓝 (V y)):= by
   apply Metric.tendsto_nhds.mpr; intro ε ep
   have hz:=half_pos ep
   filter_upwards [hr.eventually hK, Metric.tendstoUniformlyOn_iff.mp h _ hz, Metric.tendsto_nhds.mp (hp.tendsto.comp hr) _ hz] with i hI hi ℋ
   exact (dist_triangle _ (V (x i)) _).trans_lt ((add_lt_add ((dist_comm ..).trans_lt (hi _ hI)) ℋ).trans_eq (add_halves ε))

lemma pickT {F:Final C f S}{J:ℝ→tower S}(H':Leading F J) {H:(Bel C.book).Hierarchy}{r:ι→ℝ} {D:ι→ℕ}{P:ι→Panel S} (hr:Tendsto r L trail)(hd:Tendsto D L atTop) (hs: ∀ᶠ i in L, HouseT F.room.kernel H (r i) (D i) (P i))
    {x:ι→Points n}{y:Points n}(hy:y∈conf n)(X:Tendsto x L (𝓝 y))(d:Caps n){w:ι→MaxwellSlots C d}{v:MaxwellSlots C d} (hv:∀ j,Tendsto (fun i=>w i j) L (𝓝 (v j))):
   Tendsto (fun i=> Coast (P i) (r i) (w i) (x i)) L (𝓝 (WickGoal v y)):= by
   obtain ⟨K,hK,hk,hU⟩ := exists_compact_subset (conf_open _) hy
   exact landArea (mem_interior_iff_mem_nhds.mp hk) (vantage H' hr hd hs hK hU d hv) X ((WickGoal_tied v hy).continuousAt)

end YM.SignedWilsonExpansion.Homes
