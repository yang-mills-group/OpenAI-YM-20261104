import YM.Integration.ConditionalTreeCovarianceJets

/-! One changed physical forest in the ordinary zero-extended inverse.
The native padded operator has a constant identity on erased keys. Its
whole contribution to the fee for this change is one unit at order zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarTreeCovariance
open Lattice Wilson RG Precision Tree Matrix FreeResolvent FreeResolvent.Affine
  FreeResolvent.Mark FreeResolvent.TestD FreeResolvent.Lever Filter Set Function
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {t : S.Choices} {p : Clip} {W : PathData G}
variable {σ A : ℝ} {n : ℕ}
variable (hs : 0 < σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S)

/-- Zero extension to the raw keys, for either the cut or the full physical path family. -/
def observed (F : Forest S.ratio) (t : S.Choices) (p : Clip) (W : PathData G) (q : Admit)
    (B : Vec G c 1) := action (whole S F t p W q) 0 B - Shell.off (freeTo G S F)

include hs ha hW he
private theorem family {F U : Forest S.ratio} {v : Site c} (h : changed S F U v) (q : Admit)
    {θ : ℝ} (hθ : θ ∈ Icc (0:ℝ) 1) :
    let d := width G S.patch S.kernel p n A σ
    let H := crest S t (W:=W) (T:=F) (U:=U) (p:=p) q
    Bundle (guides (ray G c)) (park (native c) hearth d v) (native c) (home S) (home S)
      (action H 0) (0,θ) n (4*(n+1:ℕ)*d) (earnings G S.patch S.kernel p n A σ) := by
  intro d H
  have hP := gauged G S.patch S.kernel p n hs ha
  simpa [earnings,drain] using (mast S t hs ha hW he h q hθ).volume_price hP (u:=0)
    le_rfl (position_move _ _ hP.pos.le) (home_volume S 1 _ hP.pos)

/-- Original two-sided Schur bound on one changed tree, before removal of the erased diagonal. -/
theorem padded {F U : Forest S.ratio} {v : Site c} (h : changed S F U v) (q : Admit)
    (l : List (raw G c)) (hl : l.length < n) :
    let d := width G S.patch S.kernel p n A σ
    Here (ray G c) (native c) (home S) hearth d (4*(n+1:ℕ)*d) v l
      (earnings G S.patch S.kernel p n A σ)
      (action (whole S F t p W q) 0) (action (whole S U t p W q) 0) := by
  intro d
  let H := crest S t (W:=W) (T:=F) (U:=U) (p:=p) q
  refine paid (G:=action H 0) ?_ ?_ hl (fun θ hθ => family hs ha hW he h q hθ) <;> intro B
  · exact congrArg (fun Q => resolve Q 0) (now F U t p q B)
  · exact congrArg (fun Q => resolve Q 0) (thenAt F U t p q B)

theorem smooth (F : Forest S.ratio) (q : Admit) :
    ContDiffAt ℝ n (action (whole S F t p W q) 0) 0 := by
  have h : changed S F F (0:Site c) := fun _ _ => Iff.rfl
  have hb := restricted 0 (family hs ha hW he (n:=n) (t:=t) (p:=p) h q
    (Set.left_mem_Icc.mpr zero_le_one))
  exact (hb.glue (Eventually.of_forall fun B =>
    congrArg (fun Q => resolve Q 0) (now F F t p q B))).smooth

private theorem positive_jet (F : Forest S.ratio) (q : Admit) (l : List (raw G c)) (hl : l ≠ []) :
    jet (ray G c) (observed F t p W q) l 0 = jet (ray G c) (action (whole S F t p W q) 0) l 0 := by
  change jet _ (fun B => action (whole S F t p W q) 0 B - Shell.off _) l 0 = _
  rw [jet_sub _ _ (smooth hs ha hW he F q) contDiffAt_const,jet_const _ _ hl,sub_zero]

/-- Every positive field-order physical active-kernel derivative has the original
one-tree bound with no erased-key charge. -/
theorem positive {F U : Forest S.ratio} {v : Site c} (h : changed S F U v) (q : Admit)
    (l : List (raw G c)) (h₀ : l ≠ []) (hl : l.length < n) :
    let d := width G S.patch S.kernel p n A σ
    Here (ray G c) (native c) (home S) hearth d (4*(n+1:ℕ)*d) v l
      (earnings G S.patch S.kernel p n A σ) (observed F t p W q) (observed U t p W q) := by
  intro d
  constructor
  intro i j
  dsimp only
  rw [positive_jet hs ha hW he F q l h₀,positive_jet hs ha hW he U q l h₀]
  exact (padded hs ha hW he h q l hl).test i j

omit hs ha hW he
/-- The actual inactive projector has support on the changed diagonal at its real parent. -/
theorem pinned_away {F U : Forest S.ratio} {v : Site c} (h : changed S F U v) (i j : raw G f)
    (hi : i ≠ j ∨ home S i ≠ v) : Shell.off (freeTo G S U) i j = Shell.off (freeTo G S F) i j := by
  have hmask := suits G v h
  simp only [Shell.off_test]
  rcases hi with hij|hr
  · simp [hij]
  · simp only [hmask i hr]

/-- On either side of a Schur estimate every inactive row contains at most
one unit, at the very same physical fine key. All positive derivatives vanish. -/
private theorem inactive (F : Forest S.ratio) (δ a : ℝ) (n : ℕ) :
    Bundle (ray G c) (positions (native c) hearth δ) (native c) (home S) (home S)
      (fun _ : Vec G c 1 => Shell.off (freeTo G S F)) 0 n a 1 := by
  let e := freeTo G S F
  have htrans : (Shell.off e).transpose=Shell.off e := by
    ext i j
    by_cases hij : i=j
    · subst j; rfl
    · simp [Matrix.transpose_apply,Shell.off_test,hij,Ne.symm hij]
  refine ⟨contDiffAt_const,fun l _ => ?_⟩
  by_cases hz : l=[]
  · subst l
    rw [zeroth]
    have hrow : Rates (positions (native c) hearth δ) (native c) (home S) (home S) ([] : List (raw G c)) a 1 (Shell.off e) := by
      constructor
      intro i
      have hc (j : raw G f) : (native c).weight a (home S i) (home S j)*|Shell.off e i j|≤(if j=i then (1:ℝ) else 0) := by
        by_cases hij : j=i
        · subst j
          rw [Shell.off_test]
          by_cases he : i ∈ Set.range e <;> simp [he]
        · simp [Shell.off_test,hij,Ne.symm hij]
      simpa [Mark.pay] using Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hc j)
    exact ⟨hrow,by rw [htrans]; exact hrow⟩
  · rw [jet_const _ _ hz]
    exact ⟨Mark.Rates.zero zero_le_one,Mark.Rates.zero zero_le_one⟩

include hs ha hW he
/-- The true undifferenced raw inverse has a two-sided summed Schur bound,
including every independent coarse ray. Neither active chart size nor number
of translated faces enters its price. -/
theorem ordinary (F : Forest S.ratio) (q : Admit) :
    let d := width G S.patch S.kernel p n A σ
    Bundle (ray G c) (positions (native c) hearth d) (native c) (home S) (home S)
      (observed F t p W q) 0 n (4*(n+1:ℕ)*d) (earnings G S.patch S.kernel p n A σ+1) := by
  intro d
  have h : changed S F F (0:Site c) := fun _ _ => Iff.rfl
  have hb := restricted 0 (family hs ha hW he (n:=n) (t:=t) (p:=p) h q (Set.left_mem_Icc.mpr zero_le_one))
  have H := hb.glue (Eventually.of_forall fun B => congrArg (fun Q => resolve Q 0) (now F F t p q B))
  have E := inactive (G:=G) F d (4*(n+1:ℕ)*d) n
  refine ⟨H.smooth.sub contDiffAt_const,fun l hl => ?_⟩
  have hjet : jet (ray G c) (observed F t p W q) l 0 =
      jet (ray G c) (fun B : Vec G c 1 => resolve (whole S F t p W q B) 0) l 0 -
      jet (ray G c) (fun _ : Vec G c 1 => Shell.off (freeTo G S F)) l 0 :=
    jet_sub (ray G c) l (smooth_of_le H.smooth hl) (smooth_of_le E.smooth hl)
  rw [hjet]
  exact (H.bound l hl).sub (E.bound l hl)

omit hs ha hW he
private theorem pinned_fee {F U : Forest S.ratio} {v : Site c} (h : changed S F U v)
    (d a : ℝ) (i j : raw G f) :
    let z := |Shell.off (freeTo G S U) i j-Shell.off (freeTo G S F) i j|
    (native c).weight d (home S i) v*((native c).weight a (home S i) (home S j)*z) ≤ 1 ∧
    (native c).weight d (home S j) v*((native c).weight a (home S j) (home S i)*z) ≤ 1 := by
  intro z
  by_cases hz : i=j ∧ home S i=v
  · obtain ⟨rfl,hr⟩ := hz
    simp only [z,hr,Cost.weight_self,one_mul,Shell.off_test]
    split_ifs <;> norm_num
  · have hz' : i≠j ∨ home S i≠v := not_and_or.mp hz
    simp [z,pinned_away h i j hz']

private theorem pay_difference {a b x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a*(b*|x-y|) ≤ a*(b*|x|) + a*(b*|y|) := by
  calc a*(b*|x-y|) ≤ a*(b*(|x|+|y|)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (abs_sub x y) hb) ha
    _ = _ := by ring

include hs ha hW he
/-- Order zero includes one local unit for the independently changed inactive keys. -/
theorem flat {F U : Forest S.ratio} {v : Site c} (h : changed S F U v) (q : Admit) (hn : 0 < n) :
    let d := width G S.patch S.kernel p n A σ
    Here (ray G c) (native c) (home S) hearth d (4*(n+1:ℕ)*d) v []
      (earnings G S.patch S.kernel p n A σ + 1) (observed F t p W q) (observed U t p W q) := by
  intro d
  constructor
  intro i j
  let a := 4*(n+1:ℕ)*d
  have hh := (padded hs ha hW he (t:=t) (p:=p) h q [] hn).test i j
  have hp := pinned_fee h d a i j
  let y := Shell.off (freeTo G S U) i j-Shell.off (freeTo G S F) i j
  let x := (action (whole S U t p W q) 0 0-action (whole S F t p W q) 0 0) i j
  have hr : (observed U t p W q 0-observed F t p W q 0) i j=x-y := by
    simp only [observed,x,y,Matrix.sub_apply]; ring
  dsimp only at hh hp ⊢
  simp only [zeroth,Mark.pay,mul_one] at hh ⊢
  rw [hr]
  exact ⟨(pay_difference (x:=x) (y:=y) (Cost.weight_pos ..).le (Cost.weight_pos ..).le).trans
    (add_le_add hh.1 hp.1),
    (pay_difference (x:=x) (y:=y) (Cost.weight_pos ..).le (Cost.weight_pos ..).le).trans
      (add_le_add hh.2 hp.2)⟩

end YM.Integration.PhysicalAffineScalarTreeCovariance
end
