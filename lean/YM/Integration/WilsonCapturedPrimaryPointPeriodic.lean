import YM.Integration.WilsonCapturedPrimaryPointWindow

/-! Periodic versus cover detector on a single issued tile. Both readings use the
same signed material tensor, including its genuine wrapping paths. The canonical
lift estimate is the pure torus argument of ProjectionAliasPrice. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonCapturedPrimaryPointPeriodic
open Function Filter Finset Lattice Laurent Wilson Exterior Stationary Source Source.Drops
open FormalBulk08 FormalBulk08.Lava FormalBulk08.Lotus FormalBulk08.Mesa FormalBulk08.Gorge
open FormalBulk08.Reef FormalBulk08.Orb FormalBulk08.Shore FormalBulk08.Kemp FormalBulk08.Rift FormalBulk08.Pose
open Planned.PrimaryIntegral295 Place Carrier Film Labels Next.Foundations
open WilsonCapturedPrimaryPointWindow
open scoped Classical Topology BigOperators ENNReal
variable {G:Gauge} {d r s:ℕ} {n:Side}

theorem lifted (n:Side) (o:Loc G 1) (v:chain (wire G n) r):
    herb (fame _) (0,o) (boil n ∘ v)≤2*herb (lake n _) (drip n (0,o)) v:=by
  let K:=herb (lake n _) (drip n (0,o)) v
  have radius (i:Fin r):size (Lattice.lift (v i).1)≤K:=by
    have h:=reached (lake n _) (Fin.cons (drip n (0,o)) v:chain (wire G n) (r+1)) i.succ (0:Fin (r+1))
    simpa [lake,drip,skit,herb,K] using h
  let q:chain (edgeL G) (r+1):=Fin.cons (0,o) (boil n ∘ v)
  have sizeAt (i:Fin (r+1)):size (q i).1≤K:=by
    cases i using Fin.cases with
    | zero => simp [q,size]
    | succ i => simpa [q,boil] using radius i
  apply known_wide _ _ _
  intro i j
  change size ((q i).1-(q j).1)≤2*K
  rw [sub_eq_add_neg]
  have add:=size_add (q i).1 (-(q j).1)
  rw [size_neg] at add
  exact add.trans ((Nat.add_le_add (sizeAt i) (sizeAt j)).trans_eq (two_mul K).symm)

theorem charged (o:Loc G 1) (r d s:ℕ):
    ∃C:ℝ,0≤C ∧ ∀{n:Side}(B:ℕ)(w:ℝ),0<w → ∀(T:Tile (wire G n) r)(A:ℝ),
      Knoxville (lake n _) w (drip n (0,o)) T A → ∀x:Fin s→Snap G d,
      ‖measured B T d s x‖≤ C*widthCost (w/2) (d*s)*A*∏j,‖x j‖:=by
  obtain ⟨C,C0,W⟩:=WilsonPhysicalProjectionHolonomyPrice.tier_price o r d s
  refine ⟨C,C0,?_⟩
  intro n B w pos T A paid x
  let normTerm:=C*widthCost (w/2) (d*s)
  have term0:0≤normTerm:=mul_nonneg C0 (zero_le_one.trans (widthCost_ge (half_pos pos) _))
  let M:=∏j,‖x j‖
  have M0:0≤M:=by dsimp [M]; positivity
  have bank:= (penn_amount paid).2
  rw [tsum_fintype] at bank
  rw [derivative]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑v:chain (wire G n) r,(normTerm*M)*(Real.exp (w*herb (lake n _) (drip n (0,o)) v)*‖T v‖):=by
      apply Finset.sum_le_sum
      intro v _
      have old:=W (w/2) (half_pos pos) x (boil n ∘ v)
      have shift:Real.exp ((w/2)*herb (fame _) (0,o) (boil n ∘ v))≤Real.exp (w*herb (lake n _) (drip n (0,o)) v):=by
        apply Real.exp_le_exp.mpr
        have cap:=mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (lifted n o v) : (_:ℝ)≤_) (half_pos pos).le
        push_cast at cap;linarith only [cap]
      have l:‖masked B T v‖≤‖T v‖:=by by_cases valid:active B v <;> simp [masked,valid]
      rw [_root_.norm_mul]
      apply (mul_le_mul l old (norm_nonneg _) (norm_nonneg _)).trans
      exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left shift term0) M0)
        (norm_nonneg (T v))).trans_eq (by dsimp only [normTerm,M];ring)
    _ = normTerm*M*(∑v,Real.exp (w*herb (lake n _) (drip n (0,o)) v)*‖T v‖):= (Finset.mul_sum ..).symm
    _ ≤ normTerm*M*A:=mul_le_mul_of_nonneg_left bank (mul_nonneg term0 M0)
    _ = _:=by dsimp only [normTerm,M];ring

theorem entered (F:Frame G d) (o:Loc G 1) (row:Letter F) (r:ℕ):
    ∃C:ℝ,0≤C ∧ ∀{n:Side}(B:ℕ)(w:ℝ),0<w → ∀(T:Tile (wire G n) r)(A:ℝ),
      Knoxville (lake n _) w (drip n (0,o)) T A →
      |(pocket F (measured B T d (slots F row)) (label F row) (mint F row)).re|≤
        C*widthCost (w/2) (d*slots F row)*A:=by
  obtain ⟨K,K0,H⟩:=pocket_cost F (label F row) (slots F row) (mint F row)
  obtain ⟨C,C0,W⟩:=charged o r d (slots F row)
  refine ⟨K*C,mul_nonneg K0 C0,?_⟩
  intro n B w pos T A paid
  have non:=mul_nonneg (mul_nonneg C0 (zero_le_one.trans (widthCost_ge (half_pos pos) (d*slots F row)))) paid.1
  exact (Complex.abs_re_le_norm _).trans ((H _ _ non (W B w pos T A paid)).trans_eq (by ring))


/-- A certified support-tail bill on the cover suffices for both readouts; the
independent periodic program is evaluated on the true finite canonical links. -/
theorem original (F:Frame G d) (o:Loc G 1) (row:Letter F) (r:ℕ) :
    ∃K:ℝ,0≤K ∧ ∀{n:Side}(B:ℕ),2*B<n.val → ∀(w:ℝ),0<w →
      ∀(T:Tile (edgeL G) r)(A E:ℝ), Knoxville (fame _) w (0,o) T A →
      Knoxville (fame _) (w/2) (0,o) (fun v=>if B≤herb (fame _) (0,o) v then T v else 0) E →
      |quote F B (sieve n T) row-pearlJ F T (mint F row)|≤
        K*(widthCost (w/2/2) (d*slots F row)+widthCost (w/2) (d*slots F row))*E := by
  obtain ⟨C,hC,torus⟩ := entered F o row r
  obtain ⟨K,hK,cover⟩ := WilsonPhysicalProjectionHolonomyPrice.entered F o row r
  refine ⟨C+K,add_nonneg hC hK,?_⟩
  intro n B fit w hw T A E paid tail
  have omitted : Knoxville (fame _) (w/2) (0,o) (lost n B T) E := by
    refine ⟨tail.1,(ENNReal.tsum_le_tsum fun v=>?_).trans tail.2⟩
    by_cases keep : retained n B v
    · simp [lost,keep]
    · have far : B≤herb (fame _) (0,o) v := Nat.le_of_not_gt (fun h=>keep (filled n B fit o v h))
      simp [lost,keep,far]
  have finite := torus (n:=n) B (w/2) (half_pos hw) (sieve n (lost n B T)) E
    (sieve_bill n (lost n B T) (0,o) (half_pos hw).le omitted)
  have infinite := cover (w/2) (half_pos hw) (lost n B T) E omitted
  rw [balance F B row o T hw paid]
  have bound := (abs_sub _ _).trans (add_le_add finite infinite)
  have hw1 : 0≤widthCost (w/2/2) (d*slots F row) :=
    zero_le_one.trans (widthCost_ge (half_pos (half_pos hw)) _)
  have hw2 : 0≤widthCost (w/2) (d*slots F row) :=
    zero_le_one.trans (widthCost_ge (half_pos hw) _)
  apply bound.trans
  have crossL := mul_nonneg (mul_nonneg hK hw1) tail.1
  have crossR := mul_nonneg (mul_nonneg hC hw2) tail.1
  nlinarith only [crossL,crossR]

end YM.Integration.WilsonCapturedPrimaryPointPeriodic
