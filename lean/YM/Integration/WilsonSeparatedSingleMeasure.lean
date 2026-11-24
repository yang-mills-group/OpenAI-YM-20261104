import YM.Integration.WilsonSeparatedFusedReadout

/-! Finite one-copy signed Wilson moments, including nongeneric near
geometries. All exterior cell levels are bought before the moving
position, replica count, and cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedSingleMeasure
open Function Filter Lattice Wilson Cells Extraction OPE OPE.Cards OPE.Orbits OPE.Log
open Frontier6.Road StressFlux.Matching Trace.Pilot Next.Phase
open WilsonMixedPlacement WilsonExteriorGeometry WilsonExteriorSeparation WilsonExteriorTrains
open WilsonWholeLimit SharedIntrinsicWilsonGrid ActualFoundryDetectorSource ContinuumIntrinsicWilsonProduct
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I E : Type} [Fintype I] [Fintype E] {d : I → ℕ} {D : ℕ}

private theorem oneAxis (x : E4) {a : ℝ} (pos : 0 ≤ a) (margin : 2*a < ‖x‖) :
    ∃ i : Axis,a < |x i| := by
  by_contra! small
  have square := (sq_lt_sq₀ (mul_nonneg zero_le_two pos) (norm_nonneg x)).2 margin
  rw [EuclideanSpace.norm_sq_eq] at square
  have cap := Finset.sum_le_sum (s:=Finset.univ) (fun (i:Axis) _=>
    (sq_le_sq₀ (abs_nonneg _) pos).2 (small i))
  have cardinal : Fintype.card Axis=4 := rfl
  simp only [Finset.sum_const,Finset.card_univ,cardinal,nsmul_eq_mul,Nat.cast_ofNat] at cap
  simp only [Real.norm_eq_abs] at square
  linarith only [show (2*a)^2=4*a^2 by ring,cap,square]

omit [Fintype E] in
private theorem gaps {a η : ℝ} (pos : 0 ≤ a) (less : 2*a < η)
    (y : E → E4) (free : ClearOf 0 y η) :
    let x := beside (sole (0:E4)) y
    ∀ i j,i ≠ j → ∃ c : Axis,a < |x i c-x j c| := by
  intro x i j ne
  have separated : η ≤ ‖x i-x j‖ := by
    cases i with
    | inl u =>
      cases j with
      | inl v => exact (ne (congrArg Sum.inl (Subsingleton.elim u v))).elim
      | inr v => exact free.openSpace v
    | inr u =>
      cases j with
      | inl _ => rw [norm_sub_rev]; exact free.openSpace u
      | inr v => exact free.spread u v fun e=>ne (congrArg Sum.inr e)
  exact oneAxis (x i-x j) pos (less.trans_le separated)

/-- The literal mixed placements on named physical meshes. These margins
can be purchased anew at a moving exterior scale without changing the
cutoff statistic. -/
theorem atLevels (f : Extraction.Order) {η : ℝ} {b q n : ℕ} (hbq : b ≤ q) (hqn : q ≤ n)
    (hb : 2*C.S.a b < η) (between : 10*C.S.a q < C.S.a b)
    (far : (Fintype.card E:ℝ)*6*C.S.a n < C.S.a q) :
    ∀ y : E → E4, ClearOf 0 y η →
      ∀ m : ℕ, ∀ᶠ t : ℕ in atTop, ∀ᶠ s : ℕ×ℕ in f.fuse,
        Nonempty (PlacementAt C b q n hbq hqn (sole (0:E4)) y m t s.1 s.2) := by
  intro y free m
  let x := beside (sole (0:E4)) y
  have large := literal_trains_apart C (f:=f) b m x (gaps (C.S.a_pos _).le hb y free)
  filter_upwards [large] with t ht
  filter_upwards [ht,(Cards.largeMesh f).eventually_ge_atTop n] with s apart live
  have hI : (Fintype.card Unit:ℝ)*(2*(5*C.S.a q)) < C.S.a b := by
    simpa only [Fintype.card_unit,Nat.cast_one,one_mul] using (show 2*(5*C.S.a q) < C.S.a b by linarith only [between])
  have hJ : (Fintype.card E:ℝ)*(2*(3*C.S.a n)) < C.S.a q := by
    convert far using 1
    ring
  obtain ⟨off,fits⟩ := seats_for_all_grid_translates (C:=C) (p:=s.2) hbq le_rfl hqn live (sole (0:E4)) y hI hJ
  have thin : span C.S (hqn.trans live) s.2 ≤ span C.S (hbq.trans (hqn.trans live)) s.2 :=
    Nat.le_of_dvd (C.S.toDepth (hbq.trans (hqn.trans live)) s.2).count.property
      (Around.inherits (C:=C) hbq (hqn.trans live))
  let left (p:Fin m × Unit) : Fin m × (Unit⊕E) := (p.1,Sum.inl p.2)
  let right (p:Fin m × E) : Fin m × (Unit⊕E) := (p.1,Sum.inr p.2)
  have lsep : Injective left := fun i j e=>Prod.ext (congrArg (fun p : Fin m × (Unit⊕E) =>p.1) e)
    (Sum.inl.inj (congrArg (fun p : Fin m × (Unit⊕E) =>p.2) e))
  have rsep : Injective right := fun i j e=>Prod.ext (congrArg (fun p : Fin m × (Unit⊕E) =>p.1) e)
    (Sum.inr.inj (congrArg (fun p : Fin m × (Unit⊕E) =>p.2) e))
  refine ⟨{
    live := live
    offset := off
    central := fun i=>(fits (Work.B15.diag t i.1)).1 i.2
    exterior := fun i=>(fits (Work.B15.diag t i.1)).2 i.2
    central_apart := fun i j e=>apart _ (left i) (left j) (lsep.ne e)
    exterior_apart := fun i j e=>thin.trans_lt (apart _ (right i) (right j) (rsep.ne e))
    between := ?_ }⟩
  intro i j
  apply apart _ (left i) (right j)
  intro e
  have clash : (Sum.inl i.2 : Unit⊕E)=Sum.inr j.2 := congrArg (fun p : Fin m × (Unit⊕E)=>p.2) e
  cases clash

/-- One common exterior mesh for the whole positively separated family
before positions, copy count or fine regulator are selected. -/
theorem placements (f : Extraction.Order) (η : ℝ) (hη : 0 < η) (n₀ : ℕ) :
    ∃ b q n : ℕ, n₀ ≤ n ∧ ∃ hbq : b ≤ q, ∃ hqn : q ≤ n, ∀ y : E → E4, ClearOf 0 y η →
      ∀ m : ℕ, ∀ᶠ t : ℕ in atTop, ∀ᶠ s : ℕ×ℕ in f.fuse,
        Nonempty (PlacementAt C b q n hbq hqn (sole (0:E4)) y m t s.1 s.2) := by
  have choose (k e : ℝ) (h : 0 < e) (m : ℕ) : ∃ n:ℕ,m≤n ∧ k*C.S.a n<e := by
    have down : Tendsto (fun n=>k*C.S.a n) atTop (𝓝 0) := by simpa only [mul_zero] using (tendsto_const_nhds (x:=k)).mul C.S.shrinks
    exact ((eventually_ge_atTop m).and (down.eventually (gt_mem_nhds h))).exists
  obtain ⟨b,_,hb⟩ := choose 2 η hη 0
  obtain ⟨q,hbq,hq⟩ := choose 10 _ (C.S.a_pos b) b
  obtain ⟨n,hn,hcost⟩ := choose ((Fintype.card E:ℝ)*6) _ (C.S.a_pos q) (max q n₀)
  exact ⟨b,q,n,(le_max_right ..).trans hn,hbq,(le_max_left ..).trans hn,atLevels f hbq ((le_max_left ..).trans hn) hb hq hcost⟩

theorem one {b q n t N p Q : ℕ} {hbq : b ≤ q} {hqn : q ≤ n}
    (F : Spec.Final C f S) (y : E → E4) (atSite : PlacementAt C b q n hbq hqn (sole (0:E4)) y 1 t N p)
    (before : q ≤ Q) (de : E → ℕ) (w : Labels S de) {Y : Config G (C.side N p) → ℂ}
    {a : ℝ} (centered : PaidAt C.S N p Q (C.beta N p) a Y) (B : E → ℝ)
    (outside : ∀ i,PaidAt C.S N p n (C.beta N p) (B i) (C.O N p (S.representative _ (w i)) 0)) :
    ‖Wilson.moment (C.beta N p) (Y*product y w N p)‖ ≤ a*∏ i,B i := by
  have price := atSite.price F.room.cutoff before centered.live (fun _:Unit=>a) B (fun _=>Y)
    (fun i=>C.O N p (S.representative _ (w i.2)) 0) (fun _=>centered) (fun j=>outside j.2)
  have train0 (x:E4) : train C b t 0 x=x := by
    apply PiLp.ext
    intro i
    simp [train,Schedule.gridPoint,Work.B15.diag]
  have hz : ceilSite C N p (0:E4)=0 := by
    simp [ceilSite,show (fun _:Axis=>(0:ℤ))=(0:Cover) from rfl]
  have shift0 (U:Config G (C.side N p)) : translate (0:Site (C.side N p)) U = U := by
    funext e
    simp [Lattice.translate]
  simp only [Fintype.prod_prod_type,Fintype.prod_unique,pow_one] at price
  convert price using 3
  funext V
  change Y V*(∏ i,C.O N p (S.representative _ (w i)) (ceilSite C N p (y i)) V) =
    Y (translate (ceilSite C N p (train C b t 0 0)) V)*(∏ i,C.O N p (S.representative _ (w i)) 0
      (translate (ceilSite C N p (train C b t 0 (y i))) V))
  rw [train0,hz,shift0]
  apply congrArg (fun a:ℂ=>Y V*a)
  apply Finset.prod_congr rfl
  intro i _
  rw [train0]
  simpa only [zero_add] using (C.translation 0 (ceilSite C N p (y i)) (S.representative _ (w i)) V).symm

/-- The unselected hierarchy requires only actual separation of the
near/exterior points.  No pair of near positions must be different
in every coordinate. The price holds for every measured cluster point
simultaneously on the fixed clearance and independent label balls. -/
theorem original (F : Spec.Final C f S) (fac : Facilities C f S) (anchor : I)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (P : Plan C D (Fintype.card I) (∑ i,d i)) (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J)
    (v : (i:I) → (Climb.Bel C.book).Field (d i)) {g : ℝ → ℝ} (hg : Coupling G g) (hG : G.Simple)
    (de : E → ℕ) (R : E → ℝ) (Rpos : ∀ i,0 < R i) (η : ℝ) (ηpos : 0 < η) (k : ℕ) (ε : ℝ) (εpos : 0 < ε) :
    ∀ᶠ r in trail, ∀ x : I → Cover, Plot C (P.b r) (P.middle r) (P.j r) x →
      (∃ z : C.label D,Cluster F Q J v r (P.b r) (P.j r) x z) ∧
      ∀ z : C.label D,Cluster F Q J v r (P.b r) (P.j r) x z →
        ∀ y : E→E4, ClearOf 0 y η → Injective (beside (C.S.gridPoint (P.j r) ∘ x) y) →
        ∀ w : Labels S de, (∀ i,‖S.representative _ (w i)‖ ≤ R i) →
        ‖whole S (C.S.gridPoint (P.j r) ∘ x) (PhysMS.Frame.born J r v) y w -
          upon S D 0 y w (S.project D z)‖ ≤ ε*g r^k*r^D := by
  classical
  obtain ⟨fee,rate,_,paid⟩ := WilsonSeparatedPhysicalCopies.purchased F fac anchor Q P J H v
  obtain ⟨n₀,A,_,ext⟩ := exterior_bounds F de R Rpos 1 one_pos
  obtain ⟨o,u,n,hn,hou,hun,geometry⟩ := placements (C:=C) (E:=E) f η ηpos n₀
  let B (i:E) := A i*C.S.a n^(-(de i:ℝ)-1)+1
  have lo := rate.mul (RateLE.const (∏ i,B i) PhysMS.to_log_zoom)
  have hi := ((RateIs.const PhysMS.to_log_zoom εpos).mul ((PhysMS.coupling_rate hg hG).power k)).mul
    (PhysMS.length_rate.power D)
  have small := hi.outweigh lo (by simp only [mul_zero,zero_add,mul_neg,mul_one,add_zero]; linarith only) PhysMS.to_log_zoom
  filter_upwards [paid,small,P.coarse.grows.eventually_ge_atTop u,exists_cluster F fac anchor Q P J v]
    with r bill enough ub choose
  intro x plot
  refine ⟨choose x plot,?_⟩
  intro z hz y free sep w bounded
  obtain ⟨l,live,sub,found⟩ := hz
  letI := live
  have out : Injective (beside (sole (0:E4)) y) := by
    apply beside_distinct.mpr
    refine ⟨injective_of_subsingleton _,(beside_distinct.mp sep).2.1,?_⟩
    intro _ i he
    have nonzero := ηpos.trans_le (free.openSpace i)
    change (0:E4)=y i at he
    rw [he,sub_self,norm_zero] at nonzero
    exact (lt_irrefl _ nonzero)
  obtain ⟨t,placed⟩ := (geometry y free 1).exists
  have joined := WilsonSeparatedFusedReadout.original F fac.toServices Q J v r _ _ x y w sep out sub found
  apply (le_of_tendsto joined.norm ?_).trans ((Real.le_norm_self _).trans enough)
  filter_upwards [((bill x plot).and (placed.and (ext n hn 1 one_pos))).filter_mono sub] with s seen
  obtain ⟨cell⟩ := seen.2.1
  exact one F y cell ub de w seen.1 B (seen.2.2 (fun i=>S.representative _ (w i)) bounded)

end YM.Integration.WilsonSeparatedSingleMeasure
