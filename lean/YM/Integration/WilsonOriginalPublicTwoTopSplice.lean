import YM.Integration.WilsonPositionProgramOrderedPinReturn

/-! Add back exactly the first mixed pages above a restart on the same dated quiet. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalPublicTwoTopSplice
open Function Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open scoped BigOperators Classical
variable {G : Gauge} {a e u k m K N : ℕ} {E W V W' L : Credit}
variable {Q : Fin (a+1) → SealR G} {H : Hol G} {R : Realm G (e+1) E}

/-- The two differences have exactly the same intermediate regulated print. -/
theorem across {A δ : ℝ} {X Y Z : Era G ℝ}
    (x : Fringed k e u 1 A δ X Z) (y : Fringed k e u 1 A δ Y Z) :
    Fringed k e u 1 (2*A) δ X Y := by
  refine ⟨x.inkV,y.inkV,x.crest,fun i r hi => ?_⟩
  have hx := x.heapS i r hi
  have hy := y.rot.heapS i r hi
  have hA : A ≤ 2*A := by linarith [x.nn]
  refine ⟨hx.wax.more hA,hy.wane.more hA,?_⟩
  have h := hx.toll.plus hy.toll (by norm_num)
  rwa [sub_add_sub_cancel,← two_mul,← mul_assoc] at h

/-- Both terms have the same top N in their quiet, with only the marks restarted at K. -/
theorem history (hr : HorizonP H R W V Q) (F : Wilt Q) (X : Herit Q) (y : ℝ) (o : CellR)
    (open' : R.anchor ≤ m) (base : m ≤ K) (fine : K ≤ N) :
    loadK R.draws R.paid F X m N N y o =
      loadK R.draws R.paid F X m K N y o +
        ∑ j ∈ range (N-K), stopX R.draws R.paid F X m (K+j) N y o := by
  let C := fun i => loadK R.draws R.paid F X m (min i N) N y o
  have add (l : ℕ) : C (K+l) = C K + ∑ j ∈ range l, stopX R.draws R.paid F X m (K+j) N y o := by
    induction l with
    | zero => simp
    | succ l ih =>
      have step : C ((K+l)+1) = C (K+l) + stopX R.draws R.paid F X m (K+l) N y o :=
        tip_pay hr F X open' (by omega) (base.trans fine) o
      rw [Nat.add_succ,step,ih,sum_range_succ,add_assoc]
  simpa [C,min_eq_left fine,Nat.add_sub_of_le fine] using add (N-K)

/-- Both charts and their source certificates are selected before the cutoff or the retained face. -/
theorem original (H : Hol G) (Q : Fin (a+1) → SealR G) (E W V W' L : Credit) (e u : ℕ) :
    ∃ C C' : Credit, ∀ (R : Realm G (e+1) E), HorizonP H R W V Q →
    SpringD R (capP Q) u (capP Q+2) W' → Dormitory R (capP Q) u L →
    ∀ (m K N : ℕ) (F : Wilt Q) (X Y : Herit Q) (A B : Fin (a+1) → ℝ) (Z y δ : ℝ) (o : CellR),
    R.anchor ≤ m → m ≤ K → K ≤ N → R.y m ≤ Z → Bough Q F y Z B →
    R.tempC m K ≤ δ → Sitting Q A e δ X Y →
    let T := ∏ i, B i*A i
    Fringed (capP Q) e u 1 (2*(C.buy Z*T)) δ
      (loadK R.draws R.paid F X m N N y o)
      (loadK R.draws R.paid F X m K N y o) ∧
    ∀ i, K ≤ i → Fringed (capP Q) e u 1 (C'.buy Z*R.tempC m i*T) δ
      (stopX R.draws R.paid F X m i N y o) 0 := by
  obtain ⟨C,hC⟩ := topDay H Q E W V W' L e u
  obtain ⟨C',hC'⟩ := PalmR H Q E W V W' L e u
  refine ⟨C,C',?_⟩
  intro R hp hd ht m K N F X Y A B Z y δ o op base fine room sites rate match'
  let joint := hC R hp hd ht
  have full := joint m N K N K F X Y A B Z y δ o op (base.trans fine) base fine le_rfl room sites rate match'
  have restart := joint m K K N K F X Y A B Z y δ o op base base fine le_rfl room sites rate match'
  simp only [min_self,min_eq_left fine,min_eq_right fine] at full restart
  refine ⟨across full restart,?_⟩
  intro i late
  have first := hC' R hp hd ht m i K N K F X Y A B Z y δ o op (base.trans late) base fine le_rfl
    room sites rate match'
  have empty : stopX R.draws R.paid F Y m i K y o = 0 := by simp [stopX,not_lt.mpr late]
  simpa only [empty] using first
end YM.Integration.WilsonOriginalPublicTwoTopSplice
end
