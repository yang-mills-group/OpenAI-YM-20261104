import YM.Integration.WilsonSeparatedMovingCells

/-! Keep independently prescribed physical exterior inputs in their own
moving frame.  Their original representative norms are paid from the
strict spatial surplus of the common signed center. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOwnLength
open Function Filter Lattice Cells Wilson Extraction OPE OPE.Cards OPE.Orbits OPE.Log
open Frontier6.Road Trace.Pilot
open SharedIntrinsicWilsonGrid ContinuumIntrinsicWilsonProduct
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I E : Type} [Fintype I] [Fintype E] {d : I → ℕ} {de : E → ℕ} {D : ℕ}

private theorem roster (F : Spec.Final C f S) (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J)
    (k : ℕ) (v : (Climb.Bel C.book).Field k) {a : ℝ} (ha : 0<a) :
    RateLE trail LogV (fun r=>S.representative k (J (r^a) k v)) 0 := by
  let L := (S.representative k).toContinuousLinearMap
  have top := PhysMS.Frame.upper F k J H 0 (Nat.zero_le _) L (fun p hp=>by
    rw [show p=0 from (Submodule.mem_bot ..).mp hp,map_zero])
  simp only [Nat.cast_zero,neg_zero] at top
  have topNorm : RateLE trail LogV (fun r=>‖PhysMS.Frame.pulling k J L r‖) 0 := by
    intro q hq
    filter_upwards [top q hq] with r hr
    change ‖‖PhysMS.Frame.pulling k J L r‖‖ ≤ _
    rw [Real.norm_of_nonneg (ContinuousLinearMap.opNorm_nonneg _)]
    exact hr
  have bound := topNorm.mul (RateLE.const ‖v‖ PhysMS.to_log_zoom)
  simp only [add_zero] at bound
  have actual : RateLE trail LogV (fun s=>S.representative k (J s k v)) 0 :=
    bound.of_norm_le (Eventually.of_forall fun r=>(PhysMS.Frame.pulling k J L r).le_opNorm v)
  have time := PhysMS.length_rate.rpow a
  have toTime : Tendsto (fun r:ℝ=>r^a) trail trail := tendsto_nhdsWithin_iff.mpr
    ⟨time.tends (by linarith only [ha]) PhysMS.to_log_zoom,time.pos⟩
  intro q hq
  filter_upwards [toTime.eventually (actual (q/a) (div_pos hq ha)),PhysMS.length_rate.pos] with r hr hpos
  change 0 < r at hpos
  have identity : LogV (r^a)=a*LogV r := by
    simp only [LogV,Real.log_inv,Real.log_rpow hpos]
    ring
  rw [identity,←mul_assoc,div_mul_cancel₀ _ ha.ne'] at hr
  exact hr

private theorem factor (T : Table C.book) (Tlaw : T.Hierarchy)
    (x : I → E4) (v : Labels S d) (y : E → E4) (w : Labels S de) (z : S.Field D)
    (sep : Injective (beside x y)) (outside : Injective (beside (sole (0:E4)) y))
    (m : E → ℝ) (hm : ∀ i,0 ≤ m i) :
    ‖whole T x v y (fun i=>(m i:ℂ) • w i)-upon T D 0 y (fun i=>(m i:ℂ) • w i) z‖ =
      (∏ i,m i)*‖whole T x v y w-upon T D 0 y w z‖ := by
  let A : MultilinearMap ℂ (fun i=>S.Field (de i)) ℂ :=
    sectionLabels v (Orbits.moment T (beside y x) (d:=Sum.elim de d))
  let B : MultilinearMap ℂ (fun i=>S.Field (de i)) ℂ := sectionLabels (fun _:Unit=>z)
    (Orbits.moment T (beside y (sole (0:E4))) (d:=Sum.elim de (fun _:Unit=>D)))
  let M := A-B
  have sample (u:Labels S de) : M u = whole T x v y u-upon T D 0 y u z := by
    change A u-B u=_
    rw [show A u=whole T y u x v from sectionLabels_apply ..,
      show B u=whole T y u (sole (0:E4)) (sole z:Labels S (fun _:Unit=>D)) from sectionLabels_apply ..]
    rw [whole_flip v u x y Tlaw sep,
      whole_flip (sole z:Labels S (fun _:Unit=>D)) u (sole (0:E4)) y Tlaw outside]
    rfl
  rw [←sample,←sample,M.map_smul_univ,norm_smul,norm_prod]
  simp only [Complex.norm_real,Real.norm_of_nonneg (hm _)]

/-- The far fields themselves may be independently fixed vectors at
their own length r^a.  The common actual cutoff cluster is selected
before all real exterior positions; the radius exponent b is paid
with all its dimension-dependent mesh losses. -/
theorem original (F : Spec.Final C f S) (fac : Facilities C f S) (anchor : I)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (P : Plan C D (Fintype.card I) (∑ i,d i)) (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J)
    (v : (i:I) → (Climb.Bel C.book).Field (d i)) (w : (i:E) → (Climb.Bel C.book).Field (de i))
    {g : ℝ → ℝ} (hg : Coupling G g) (hG : G.Simple) {a b : ℝ} (ap : 0 < a) (bp : 0 < b)
    (inside : 3*b < P.h) (reserve : (∑ i,((de i:ℝ)+1)*(4*b)) < 1/32)
    (k : ℕ) (ε : ℝ) (εpos : 0 < ε) :
    ∀ᶠ r in trail, ∀ x : I → Cover, Plot C (P.b r) (P.middle r) (P.j r) x →
      (∃ z : C.label D,Cluster F Q J v r (P.b r) (P.j r) x z) ∧
      ∀ z : C.label D,Cluster F Q J v r (P.b r) (P.j r) x z →
        ∀ y : E → E4, ClearOf 0 y (r^b) → Injective (beside (C.S.gridPoint (P.j r) ∘ x) y) →
          let W := PhysMS.Frame.born J (r^a) w
          (‖whole S (C.S.gridPoint (P.j r) ∘ x) (PhysMS.Frame.born J r v) y W -
            upon S D 0 y W (S.project D z)‖ ≤ ε*g r^k*r^D) ∧
          (Screen (C.S.gridPoint (P.j r) ∘ x) → ∀ s : Viewers F,
            ‖whole (spectator F s) (C.S.gridPoint (P.j r) ∘ x) (PhysMS.Frame.born J r v) y W -
              upon (spectator F s) D 0 y W (S.project D z)‖ ≤ ε*g r^k*r^D) := by
  classical
  let t := (1/32-(∑ i,((de i:ℝ)+1)*(4*b)))/2
  have gain : 0<t := by dsimp only [t]; linarith only [reserve]
  have room : t+(∑ i,((de i:ℝ)+1)*(4*b))<1/32 := by dsimp only [t]; linarith only [reserve]
  let W (r:ℝ) := PhysMS.Frame.born J (r^a) w
  let m (i:E) (r:ℝ) := 1+‖S.representative _ (W r i)‖
  have hpos (i:E) (r:ℝ) : 0 < m i r := by dsimp only [m]; positivity
  have costs (i:E) : RateLE trail LogV (m i) 0 :=
    (RateLE.const (1:ℝ) PhysMS.to_log_zoom).add (roster F J H (de i) (w i) ap).norm PhysMS.to_log_zoom
  have total := RateLE.prod (S:=Finset.univ) PhysMS.to_log_zoom (fun i _=>costs i)
  have pay := (RateIs.const PhysMS.to_log_zoom (zero_lt_one: (0:ℝ)<1)).outweigh
    (total.mul ((PhysMS.length_rate.rpow t).pays PhysMS.to_log_zoom))
      (by simp only [Finset.sum_const_zero,zero_add,mul_neg,mul_one]; exact neg_lt_zero.mpr gain) PhysMS.to_log_zoom
  have base := WilsonSeparatedMovingCells.original F fac anchor Q P J H v hg hG de (fun _=>1)
    (fun _=>one_pos) bp inside t room k ε εpos
  filter_upwards [base,pay,PhysMS.length_rate.pos,hg.positive] with r method charged positive active
  intro x plot
  obtain ⟨exist,rows⟩ := method x plot
  refine ⟨exist,?_⟩
  intro z hz y free sep
  let u : Labels S de := fun i=>((m i r:ℂ)⁻¹) • W r i
  have bounded (i:E) : ‖S.representative (de i) (u i)‖ ≤ 1 := by
    dsimp only [u]
    rw [map_smul,norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (hpos i r).le]
    exact (inv_mul_le_one₀ (hpos i r)).mpr (by dsimp only [m]; linarith only)
  have matched : W r=fun i=>(m i r:ℂ) • u i := by
    funext i
    have hn : (m i r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hpos i r).ne'
    simp only [u,smul_smul,mul_inv_cancel₀ hn,one_smul]
  have out : Injective (beside (sole (0:E4)) y) := by
    refine beside_distinct.mpr ⟨injective_of_subsingleton _,(beside_distinct.mp sep).2.1,?_⟩
    intro _ i e
    have away := (Real.rpow_pos_of_pos positive b).trans_le (free.openSpace i)
    change (0:E4)=y i at e
    rw [e,sub_self,norm_zero] at away
    exact lt_irrefl _ away
  obtain ⟨one,many⟩ := rows z hz y free sep u bounded
  let target := ε*g r^k*r^D
  have nonnegative : 0 ≤ target := by dsimp only [target]; positivity
  have enough : (∏ i,m i r)*(target*r^t) ≤ target := by
    rw [show (∏ i,m i r)*(target*r^t)=target*((∏ i,m i r)*r^t) by ring]
    exact mul_le_of_le_one_right nonnegative ((Real.le_norm_self _).trans charged)
  have price (T:Table C.book) (hT:T.Hierarchy)
      (bound : ‖whole T (C.S.gridPoint (P.j r) ∘ x) (PhysMS.Frame.born J r v) y u -
        upon T D 0 y u (S.project D z)‖ ≤ target*r^t) :
      ‖whole T (C.S.gridPoint (P.j r) ∘ x) (PhysMS.Frame.born J r v) y (W r) -
        upon T D 0 y (W r) (S.project D z)‖ ≤ target := by
    rw [matched,factor T hT _ _ y u _ sep out (fun i=>m i r) (fun i=>(hpos i r).le)]
    exact (mul_le_mul_of_nonneg_left bound (Finset.prod_nonneg fun i _=>(hpos i r).le)).trans enough
  exact ⟨price S F.room.kernel one,fun screen s=>price _ (spectate F s) (many screen s)⟩

end YM.Integration.WilsonSeparatedOwnLength
