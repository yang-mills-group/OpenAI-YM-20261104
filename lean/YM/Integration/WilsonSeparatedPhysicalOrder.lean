import YM.Integration.WilsonSeparatedPhysicalView

/-! The paid separated-foreground estimate in the physical coupling and
at the engineering power of the fused output.  Exterior prices and
the physical mesh are chosen before any field or character is read. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedPhysicalOrder
open Function Filter Lattice Cells Wilson Extraction OPE OPE.Log OPE.Cards OPE.Orbits
open OPE.Log.Trunk.Shuttle Trace.Pilot Frontier6.Road
open SharedIntrinsicWilsonGrid ActualFoundryDetectorSource ContinuumIntrinsicWilsonProduct
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I E : Type} [Fintype I] [Fintype E] {d : I → ℕ} {D : ℕ}

private theorem small (S₀ : Schedule) (a c : ℝ) (hc : 0 < c) (base : ℕ) :
    ∃ k : ℕ, base ≤ k ∧ a * S₀.a k < c := by
  have tends : Tendsto (fun k => a*S₀.a k) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x:=a)).mul S₀.shrinks
  exact ((eventually_ge_atTop base).and (tends.eventually (gt_mem_nhds hc))).exists

private theorem charge {fee g : ℝ → ℝ} (hg : Coupling G g) (hG : G.Simple)
    (h : RateLE trail LogV fee (-(D:ℝ)-1/32)) (B : ℝ) (k : ℕ) (ε : ℝ) (pos : 0 < ε) :
    ∀ᶠ r in trail, fee r * B ≤ ε*g r^k*r^D := by
  have lo := h.mul (RateLE.const B PhysMS.to_log_zoom)
  simp only [add_zero] at lo
  have hi := ((RateIs.const PhysMS.to_log_zoom pos).mul ((PhysMS.coupling_rate hg hG).power k)).mul
    (PhysMS.length_rate.power D)
  simp only [mul_zero,zero_add,mul_neg,mul_one,id_eq] at hi
  exact (hi.outweigh lo (by linarith only) PhysMS.to_log_zoom).mono
    (fun r hr=>(Real.le_norm_self _).trans hr)

/-- One genuine full-product cluster is available before the exterior
is read. Every such cluster works uniformly on separated real exterior
locations, bounded physical fields and all characters. -/
theorem original (F : Spec.Final C f S) (fac : Facilities C f S) (anchor : I)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (P : Plan C D (Fintype.card I) (∑ i,d i))
    (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J)
    (v : (i : I) → (Climb.Bel C.book).Field (d i))
    {g : ℝ → ℝ} (hg : Coupling G g) (hG : G.Simple)
    (de : E → ℕ) (R : E → ℝ) (Rpos : ∀ i,0 < R i) (η : ℝ) (ηpos : 0 < η)
    (k : ℕ) (ε : ℝ) (εpos : 0 < ε) :
    ∀ᶠ r in trail, ∀ x : I → Cover, Plot C (P.b r) (P.middle r) (P.j r) x →
      Screen (C.S.gridPoint (P.j r) ∘ x) →
        (∃ z : C.label D, Cluster F Q J v r (P.b r) (P.j r) x z) ∧
        ∀ z : C.label D, Cluster F Q J v r (P.b r) (P.j r) x z →
          ∀ (y : E → E4), ClearOf 0 y η → Injective (beside (C.S.gridPoint (P.j r) ∘ x) y) →
          ∀ w : Labels S de, (∀ i, ‖S.representative _ (w i)‖ ≤ R i) →
          ∀ s : Viewers F, ‖whole (spectator F s) (C.S.gridPoint (P.j r) ∘ x) (PhysMS.Frame.born J r v) y w -
            upon (spectator F s) D 0 y w (S.project D z)‖ ≤ ε*g r^k*r^D := by
  classical
  obtain ⟨fee,rate,_,paid⟩ := WilsonSeparatedPhysicalCopies.purchased F fac anchor Q P J H v
  obtain ⟨n₀,A,_,ext⟩ := exterior_bounds F de R Rpos 1 one_pos
  obtain ⟨o,_,ho⟩ := small C.S 2 η ηpos 0
  obtain ⟨u,hou,hu⟩ := small C.S 10 (C.S.a o) (C.S.a_pos _) o
  obtain ⟨n,hn,hn'⟩ := small C.S ((Fintype.card E:ℝ)*6) (C.S.a u) (C.S.a_pos _) (max u n₀)
  let cost (i:E) := A i*C.S.a n^(-(de i:ℝ)-1)+1
  have count := charge hg hG rate (∏ i,cost i) k ε εpos
  filter_upwards [paid,count,P.coarse.grows.eventually_ge_atTop u,exists_cluster F fac anchor Q P J v]
    with r bill enough ub choose
  intro x plot screen
  refine ⟨choose x plot,?_⟩
  intro z hz y free sep w bounded s
  have hall : Hall C.S o u (P.b r) u n 1 (Fintype.card E) := by
    refine ⟨hou,le_rfl,ub,(le_max_left ..).trans hn,?_,?_⟩
    · simpa only [Nat.cast_one,one_mul] using (show 2*(5*C.S.a u) < C.S.a o by linarith only [hu])
    · convert hn' using 1
      ring
  have prep : Prepared (C:=C) (names w) f n cost :=
    ⟨fun i => (ext n ((le_max_right ..).trans hn) 1 one_pos).mono fun t ht =>
      ht (fun i=>S.representative _ (w i)) bounded i⟩
  have viewer : Probe.Viewer C f (names w) (P.b r) η (∏ i,cost i) :=
    ⟨o,u,u,n,cost,hall,ho,prep,rfl⟩
  have outside : Injective (beside (sole (0:E4)) y) := by
    apply beside_distinct.mpr
    refine ⟨injective_of_subsingleton _,(beside_distinct.mp sep).2.1,?_⟩
    intro _ i he
    have hp := ηpos.trans_le (free.openSpace i)
    change (0:E4)=y i at he
    rw [he,sub_self,norm_zero] at hp
    exact (lt_irrefl _ hp)
  exact (WilsonSeparatedPhysicalView.measured F fac Q J v r _ _
    (plot.first.trans ((Nat.le_succ _).trans plot.last)) x screen y w viewer free sep outside
    (bill x plot) z hz s).trans enough

end YM.Integration.WilsonSeparatedPhysicalOrder
