import YM.Pert.Scale.Bank
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace YM.Pert.Scale
open Maxwell Extra.FD Labels Function Position Set Topology RawLabels Table
open Maxwell.Wick
open scoped ContDiff
variable {G : Gauge} {F : Frames G} {d n : ℕ}
lemma rare (B : RStage F d) (i : Fin (B.m+1)) (t : ℝ) : gear F d t (B.b i) = (t:ℂ)^((B.w i).1) • B.b i := by
  obtain ⟨j,h⟩ := B.corners i
  have he : pack F j=enroll F d ((F.level d).basis j) := rfl
  let w := ((F.level d).grades j).1
  have hw : w=(B.w i).1 := by
    refine MvPolynomial.IsWeightedHomogeneous.inj_right (φ:=writes F d (B.b i)) ?_ ?_ (B.weighs i)
    · exact fun he => B.b.ne_zero i ((writes_inj F d) (he.trans ((writes F d).map_zero.symm)))
    intro v hv
    let hi := (at_alcove F d j) (h ▸ hv)
    exact congrArg Prod.fst ((weight_collapse v).symm.trans hi)
  rw [← hw, h,he,gear_inherit, grow_weights (p:= (F.level d).basis j) (fun v hv => ?_) t,map_smul]
  let hi := (pure_grade _ _ |>.mp ((F.level d).pure j)) hv
  exact congrArg Prod.fst ((weight_slot v).symm.trans hi)

def panels (B : RStage F d) : Buffer F d →ₗ[ℝ] (Fin (B.m+1) → E F d) where
  toFun b i := b.val (B.b i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
lemma panels_injective (B : RStage F d) : Injective (panels B) := by
  intro x y hy; apply Subtype.ext; ext p
  change x.val p=y.val p
  rw [←B.b.sum_equivFun p,map_sum,map_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Rigid.dispatch_cmul,Rigid.dispatch_cmul]
  exact congrArg (_ • ·) (congrFun hy i)

/-- The engineering increment a polynomial of relative length. -/
lemma bank_diff (B : RStage F d) : ContDiff ℝ ω (bank F d) := by
  let y : Buffer F d →ₗ[ℝ] (Fin (B.m+1) → E F d) := panels B
  have hk : LinearMap.ker y=⊥ := by
    apply le_antisymm ?_ bot_le; intro v hv
    have he : v=(0:Buffer F d) := panels_injective B ((LinearMap.mem_ker.mp hv).trans y.map_zero.symm)
    rw [he]; exact Submodule.zero_mem _
  obtain ⟨z,hz⟩ := LinearMap.exists_leftInverse_of_injective (K:=ℝ) (V:=Buffer F d) (V':=Fin (B.m+1) → E F d) y hk
  let z' : (Fin (B.m+1)→E F d)→L[ℝ] Buffer F d := LinearMap.toContinuousLinearMap (E:=Fin (B.m+1)→E F d) (F':=Buffer F d) z -- arg F'?
  let D (t : ℝ) i := (((t:ℂ)^((B.w i).1) - 1) • B.b i : E F d)
  have ht : bank F d = z' ∘ D := funext fun t => by
    change _ = z (D t)
    rw [show D t = panels B (bank F d t) from funext fun i=> Eq.symm (show (gear F d t (B.b i)-B.b i)=_ by simp only [D,sub_smul,one_smul]; rw [rare])]
    exact (congrArg (fun w : Buffer F d →ₗ[ℝ] Buffer F d => w (bank F d t)) hz).symm
  rw [ht]; exact (ContinuousLinearMap.contDiff (𝕜:=ℝ) (n:=ω) (E:=Fin (B.m+1)→E F d) (F:=Buffer F d) z').comp (f:=D) (contDiff_pi.mpr fun i =>
    ((show ContDiff ℝ ω (fun r:ℝ => (r:ℂ)^_) from Complex.ofRealCLM.contDiff.pow _).sub contDiff_const).smul contDiff_const)
lemma bank_origin (F : Frames G) (d : ℕ) : bank F d 1 = 0 := by
  let B := recorded F d
  apply panels_injective B
  funext i; change gear F d 1 (B.b i) - _ = _
  rw [rare]; simp

lemma rising_moment {x : Points n} (hx : x∈conf n) {q : Fin n → WickPol G} {w : Fin n→ℕ}
    (hw : ∀ i, Exact (q i) (w i)) {t : ℝ} (ht : t≠0) :
   moment G (t•x) (fun i => (t:ℂ)^(w i) • q i) = moment G x q := by
  rw [MultilinearMap.map_smul_univ, smul_eq_mul,sumFormula,sumFormula,Finset.mul_sum]
  refine Finset.sum_congr rfl fun u hu=> ?_
  have he : (∏ i, (t:ℂ)^w i)*monomial (t•x) u=monomial x u := by
    rw [Finset.prod_pow_eq_pow_sum]
    convert circuit u hx ht using 3
    exact Finset.sum_congr rfl fun i _=> Eq.symm (hw i (Finsupp.mem_support_iff.mp (Fintype.mem_piFinset.mp hu i)))
  rw [mul_left_comm,he]

lemma points_equ {x : Points n} (hx : x∈conf n) (q : Fin n → E F d) {t : ℝ} (ht:t≠0) :
   Ward.disc (fun i => (⟨d,gear F d t (q i)⟩:(freeTable F).Tag)) (t•x) = Ward.disc (fun i=>(⟨d,q i⟩:(freeTable F).Tag)) x := by
  let T := freeTable F
  let M := T.classMoment T (fun _ : Fin n=> d)
  suffices h : (M (t•x)).compLinearMap (fun i=>gear F d t)=M x from congrArg (fun f => f q) h
  ext1 v
  rw [Multilabel.expansion (fun _ : Fin n => (recorded F d).b), Multilabel.expansion (fun _ : Fin n => (recorded F d).b) (M x)]
  refine Finset.sum_congr rfl fun i _ => congrArg (_ • ·) ?_
  let k : Fin n→E F d := fun j => (recorded F d).b (i j)
  change T.useAt T (t•x) (fun j=>⟨d,gear F d t (k j)⟩)=T.useAt T x (fun j=>⟨d,k j⟩)
  rw [writes_eval,writes_eval]; simp only [k,rare,map_smul]
  exact rising_moment hx (fun j=> (recorded F d).weighs (i j)) ht

end YM.Pert.Scale
