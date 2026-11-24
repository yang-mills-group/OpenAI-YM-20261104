import YM.Integration.ConditionalAffineRouteJets
import YM.Integration.ConditionalAffineRetainedEndpoints

/-! Price the discarded physical transport acting on its original varying
endpoint, with the true finite colors and coarse sites summed explicitly. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.ConditionalAffineLocalizedProduct
open Function Lattice Wilson RG Precision Exterior Tree Pressure Pressure.Tube
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset FreeResolvent FreeResolvent.TestD
open ConditionalAffineCoarsePlaquettes ConditionalAffineRetainedEndpoints
open scoped BigOperators Classical Topology ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- Exact reconstruction at each physical color endpoint. -/
private theorem rebuild (M : Pay G) (v : G.Color) :
    ∑ b : G.ColorIndex, v b • M (EuclideanSpace.basisFun G.ColorIndex ℝ b) = M v := by
  calc
    _ = ∑ b : G.ColorIndex, M (v b • EuclideanSpace.basisFun G.ColorIndex ℝ b) := by simp only [map_smul]
    _ = M _ := (map_sum M _ _).symm
    _ = _ := congrArg M ((EuclideanSpace.basisFun G.ColorIndex ℝ).sum_repr v)

def multiplier (G : Gauge) (n : ℕ) (a A ξ : ℝ) :=
  2^n*(A*a)*(Fintype.card G.ColorIndex:ℝ)*torusPay Layers2 (ξ/2)

private theorem multiplier_smul (G : Gauge) (n : ℕ) (a t A ξ : ℝ) :
    multiplier G n (a*t) A ξ=multiplier G n a A ξ*t := by
  unfold multiplier
  ring


/-- The original resolved column and all varying endpoint colors are
multiplied before summing over the true coarse plaquette address. -/
theorem apply_rows (n : ℕ) (s : Signed) (x : Site c) (D : Twin c → PriceCoords G c → Pay G)
    (Y : Twin c→PriceCoords G c→G.Color) {δ ξ a A : ℝ} (hδ : 0≤δ) (hξ : 0<ξ) (hk : n*δ≤ξ/2)
    (ha : 0≤a) (hA : 0≤A)
    (hD : ∀ (j : Twin c) (b : G.ColorIndex), Point 0 (s.act x) δ n
      (fun B => D j B (EuclideanSpace.basisFun G.ColorIndex ℝ b)) (a*Real.exp (-ξ*separation x j.1.1)))
    (hY : ∀ j : Twin c, Point 0 (s.act j.1.1) δ n (Y j) A) :
    Point 0 (s.act x) δ n (fun B => ∑ j : Twin c, D j B (Y j B)) (multiplier G n a A ξ) := by
  let d (j : Twin c) : ℝ := separation x j.1.1
  let C := (2:ℝ)^n*(A*a)
  have hc : 0≤C := by unfold C; positivity
  have h (j : Twin c) (b : G.ColorIndex) : Point 0 (s.act x) δ n
      (fun B => Y j B b • D j B (EuclideanSpace.basisFun G.ColorIndex ℝ b))
      (C*Real.exp (-(ξ/2)*d j)) := by
    have hh := ((hY j).color b).shift (q:=s.act x) (by simpa only [separation_signed] using le_refl (separation x j.1.1)) hδ
    have hmul := hh.multiply (ContinuousLinearMap.lsmul ℝ ℝ) (ContinuousLinearMap.opNorm_lsmul_le (E:=G.Color)) (hD j b)
    have he : Real.exp ((n:ℝ)*δ*d j)*Real.exp (-ξ*d j)≤Real.exp (-(ξ/2)*d j) := by
      rw [←Real.exp_add,Real.exp_le_exp]
      nlinarith only [mul_le_mul_of_nonneg_right hk (show 0≤d j from Nat.cast_nonneg _)]
    have hv := mul_le_mul_of_nonneg_left he hc
    apply hmul.mono le_rfl
    simpa only [C,d,mul_one,one_mul,mul_assoc,mul_comm,mul_left_comm] using hv
  have hcol (j : Twin c) : Point 0 (s.act x) δ n (fun B => D j B (Y j B))
      ((Fintype.card G.ColorIndex:ℝ)*(C*Real.exp (-(ξ/2)*d j))) := by
    have hh := Point.sum_price Finset.univ (fun _ : G.ColorIndex => C*Real.exp (-(ξ/2)*d j)) (fun b _ => h j b)
    simpa only [rebuild,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hh
  have htot := Point.sum_price Finset.univ _ (fun j _ => hcol j)
  apply htot.mono le_rfl
  have hm : ∑ j : Twin c, Real.exp (-(ξ/2)*d j) ≤ torusPay Layers2 (ξ/2) := by
    have h := (volume c Layers2 (ξ/2) (half_pos hξ)).bound x
    rw [←(Work.E03.meshEquiv c).sum_comp] at h
    exact h
  have hh := mul_le_mul_of_nonneg_left hm (mul_nonneg (Nat.cast_nonneg (Fintype.card G.ColorIndex)) hc)
  simp only [←Finset.mul_sum]
  simpa only [multiplier,C,mul_assoc,mul_left_comm,mul_comm] using hh

private theorem expense {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {a ξ δ : ℝ} {u : PriceCoords G c→E} {y x p : Site c} (hs : ContDiffAt ℝ n u 0)
    (H : ∀ l : List (Coord G c), l.length≤n → (native c).weight ξ x y * (marks G c δ).pay l p * ‖jet Push.Uniform.bolt u l 0‖≤a) :
    Point 0 p δ n u (a*Real.exp (-ξ*separation x y)) := by
  refine ⟨hs,fun l hl => ?_⟩
  have HH := mul_le_mul_of_nonneg_right (H l hl) (Real.exp_pos (-ξ*separation x y)).le
  change (Real.exp (ξ*separation x y) * _ * _) * _ ≤ _ at HH
  rw [show ∀ M N : ℝ, (Real.exp (ξ*separation x y)*M*N)*Real.exp (-ξ*separation x y)=M*N from
    fun M N => by rw [show (Real.exp (ξ*separation x y)*M*N)*Real.exp (-ξ*separation x y)=(Real.exp (ξ*separation x y)*Real.exp (-ξ*separation x y))*(M*N) from by ring,←Real.exp_add]; simp] at HH
  exact HH

/-- The true full-minus-truncated noise transport acts on the complete
coarse signed plaquette, with all physical positions independently hit. -/
theorem noise (G : Gauge) (P : Teller G) (L : Side) (n : ℕ) : ∃ δ N : ℝ, 0<δ ∧ 0<N ∧
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), P.Funds S T → S.patch.L=L → ∀ (s : Signed) (R : ℕ) (i : Bond c),
      Point 0 (s.act i.1) δ n (fun B => Pressure.zip (fun i j => PhysicalAffineScalarUncut.noiseStack T (turn s 1 B) i j-
        T.Φ' R (turn s 1 B) i j) (fun j => value T s j B) i)
        (N*Real.exp (-(P.η/2)*((R:ℝ)/L.val))) := by
  obtain ⟨d,J,hd,hJ,H⟩ := ConditionalAffineNoiseWinding.charged G n P.η P.width
  obtain ⟨e,A,he,hA,hY⟩ := whole G P n
  let ξ := P.η/4
  have hξ : 0<ξ := by unfold ξ; have h:=P.width; positivity
  let δ := min d (min e (ξ/(2*((n:ℝ)+1))))
  have hδ : 0<δ := lt_min hd (lt_min he (div_pos hξ (by positivity)))
  have hN : (n:ℝ)*δ≤ξ/2 := by
    have hh : δ≤ξ/(2*((n:ℝ)+1)) := (min_le_right ..).trans (min_le_right ..)
    have hn := (le_div_iff₀ (by positivity : 0<2*((n:ℝ)+1))).mp hh
    nlinarith only [hn,hδ.le]
  let M := 1+|multiplier G n (J*P.C) A ξ|
  refine ⟨δ,M,hδ,by unfold M; positivity,?_⟩
  intro c f S T hP hL s R i
  let t := Real.exp (-(P.η/2)*((R:ℝ)/L.val))
  let D (j : Twin c) (B : PriceCoords G c) := PhysicalAffineScalarUncut.noiseStack T (turn s 1 B) i j-T.Φ' R (turn s 1 B) i j
  have H' (j : Twin c) (b : G.ColorIndex) := H S T P.C hP.crosses.1 s (1:Config G c) R i j
    (EuclideanSpace.basisFun G.ColorIndex ℝ b) ((EuclideanSpace.basisFun G.ColorIndex ℝ).orthonormal.norm_eq_one b).le
  have hp (j : Twin c) (b : G.ColorIndex) : Point 0 (s.act i.1) δ n (fun B => D j B (EuclideanSpace.basisFun G.ColorIndex ℝ b))
      ((J*P.C*t)*Real.exp (-ξ*separation i.1 j.1.1)) := by
    apply Point.mono (C:=((J*P.C*t)*Real.exp (-ξ*separation i.1 j.1.1))) (σ:=d) _ (min_le_left ..) le_rfl
    apply expense (ConditionalAffineNoiseWinding.regular_score T s 1 R i j _ P.width hP.crosses.1 n)
    intro l hl
    have u := H' j b l hl
    rw [show (mesh j).1=j.1.1 from rfl] at u
    simpa only [D,turn,t,hL,ξ,mul_assoc,mul_left_comm,mul_comm] using u
  have ht : 0≤t := (Real.exp_pos _).le
  have hC : 0≤P.C := Push.AbsoluteSums.budget_nonneg (hP.crosses.1 (pole i).2 (Sum.inl (plaquette (⟨(0,1),by decide⟩ : PlaqAxes))))
  have result := apply_rows n s i.1 D (value T s) hδ.le hξ hN (mul_nonneg (mul_nonneg hJ.le hC) ht) hA.le hp
    (fun j => (hY S T hP s j).mono ((min_le_right ..).trans (min_le_left ..)) le_rfl)
  apply result.mono le_rfl
  have hh := mul_le_mul_of_nonneg_right (show multiplier G n (J*P.C) A ξ ≤ M by unfold M; linarith [le_abs_self (multiplier G n (J*P.C) A ξ)]) ht
  rw [multiplier_smul]
  exact hh

theorem read_jet {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : PriceCoords G c→E) (l : List (Coord G c)) :
    jet (FreeResolvent.Affine.ray G c) (F ∘ ConditionalAffineNoiseCoordinates.arrange G c)
        (List.ofFn (ConditionalAffineNoiseCoordinates.index G c ∘ l.get)) 0 = jet Push.Uniform.bolt F l 0 := by
  rw [Stars.list_result,ConditionalAffineNoiseCoordinates.directions]
  have h : (ConditionalAffineNoiseCoordinates.index G c).symm ∘ (ConditionalAffineNoiseCoordinates.index G c ∘ l.get) = l.get := by
    funext i
    exact (ConditionalAffineNoiseCoordinates.index G c).symm_apply_apply (l.get i)
  rw [h,←Stars.list_result,List.ofFn_get]

theorem read_pay (l : List (Coord G c)) (p : Site c) (δ : ℝ) :
    (FreeResolvent.Affine.marks G c δ).pay (List.ofFn (ConditionalAffineNoiseCoordinates.index G c ∘ l.get)) p =
      (marks G c δ).pay l p := by
  rw [Stars.pays]
  change Real.exp (δ*Stars.rays (native c) p (coordRoot∘l.get))=_
  rw [←Stars.pays,List.ofFn_get]

private theorem build_color {v : PriceCoords G c→G.Color} {p : Site c} {δ Z : ℝ} {n : ℕ}
    (h : ∀ b : G.ColorIndex, Point 0 p δ n (fun x => v x b) Z) :
    Point 0 p δ n v ((Fintype.card G.ColorIndex:ℝ)*Z) := by
  let E := EuclideanSpace.basisFun G.ColorIndex ℝ
  have hh (b : G.ColorIndex) : Point 0 p δ n (fun x => v x b • E b) Z := by
    let L := (ContinuousLinearMap.id ℝ ℝ).smulRight (E b)
    have hL : ‖L‖≤1 := L.opNorm_le_bound zero_le_one (fun y => by
      change ‖y • E b‖≤1*‖y‖; rw [norm_smul,E.orthonormal.norm_eq_one,mul_one,one_mul])
    have hL' (y : ℝ) : L y=y • E b := rfl
    simpa only [hL',one_mul] using (h b).line hL
  have hv (x : PriceCoords G c) : ∑ b : G.ColorIndex, v x b • E b=v x := E.sum_repr (v x)
  simpa only [hv,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using Point.sum_price Finset.univ (fun _ : G.ColorIndex => Z) (fun b _ => hh b)

set_option maxHeartbeats 1900000 in
private theorem transported (P : Teller G) (L : Side) (n : ℕ) (T : Tube G S) (hP : P.Funds S T)
    (hL : S.patch.L=L) (s : Signed) (R : ℕ) (i : Twin f) (δ : ℝ) (hd : 0≤δ)
    (h1 : 2*n*δ≤(P.η/(4*(5*(L.val:ℝ))))/2) :
    let B5 := 5*(L.val:ℝ)
    let ξ := P.η/4
    let ν := P.η/(4*B5)
    let a := Real.exp (4*ν+3*P.η/4)*FreeResolvent.Affine.elbow G n (ν/4)*(P.C/(L.val:ℝ)^2)
    let Z := (Fintype.card G.ColorIndex:ℝ)*a
    let t := Real.exp (-(P.η/2)*((R:ℝ)/B5))
    let x := S.ratio.parent i.1.1
    let D (j : Twin c) (B : PriceCoords G c) := PhysicalAffineScalarUncut.faceStack T (turn s 1 B) i j-T.Φ R (turn s 1 B) i j
    ∀ (j : Twin c) (b : G.ColorIndex), Point 0 (s.act x) δ n (fun B => D j B (EuclideanSpace.basisFun G.ColorIndex ℝ b))
      ((Z*t)*Real.exp (-ξ*separation x j.1.1)) := by
  intro B5 ξ ν a Z t x D
  have root : S.ratio.parent (affine s 0 (mesh i).1)=s.act x := by
    simp only [x,affine,add_zero,S.ratio.parent_signed S.patch.odd_side]; rfl
  have hm : ConditionalAffineRouteJets.fee G n P.η (5*(S.patch.L.val:ℝ)) R * (P.C/(S.patch.L.val:ℝ)^2)=a*t := by
    rw [hL]; unfold ConditionalAffineRouteJets.fee a t ν B5
    rw [sub_eq_add_neg,Real.exp_add,neg_mul]; ring
  intro j b
  have hv (u : G.ColorIndex) : Point 0 (s.act x) δ n (fun B => D j B (EuclideanSpace.basisFun G.ColorIndex ℝ b) u)
      ((a*t)*Real.exp (-ξ*separation x j.1.1)) := by
    let F := fun B => D j B (EuclideanSpace.basisFun G.ColorIndex ℝ b) u
    have eq : ConditionalAffineRouteJets.faceTail T s R i j u b = F ∘ ConditionalAffineNoiseCoordinates.arrange G c := rfl
    have hs := ConditionalAffineRouteJets.face_regular P T hP s R i j u b n
    rw [eq] at hs
    have hs' : ContDiffAt ℝ n F 0 := by
      let α := ConditionalAffineNoiseCoordinates.arrange G c
      have houter : ContDiffAt ℝ n (F ∘ α) (α.symm (0:PriceCoords G c)) := by
        rw [map_zero]
        exact hs
      have hcomp := houter.comp (0:PriceCoords G c) α.symm.contDiff.contDiffAt
      have heq : ((F ∘ α) ∘ α.symm)=F := by
        funext p
        exact congrArg F (α.apply_symm_apply p)
      rwa [heq] at hcomp
    apply expense hs'
    intro l hl
    have h := ConditionalAffineRouteJets.faces P T hP s R i j u b n δ hd (by simpa only [hL,ν,B5] using h1)
      (List.ofFn (ConditionalAffineNoiseCoordinates.index G c ∘ l.get)) (by simpa only [List.length_ofFn] using hl)
    dsimp only at h
    rw [root,eq,read_jet,read_pay,hm] at h
    rw [show S.ratio.parent (mesh i).1=x from rfl,show (mesh j).1=j.1.1 from rfl] at h
    simpa only [Real.norm_eq_abs,mul_assoc,ξ] using h
  apply (build_color hv).mono le_rfl
  exact le_of_eq (by dsimp only [Z]; ring)

set_option maxHeartbeats 2600000 in
/-- The actual full-minus-truncated `mf` is multiplied by its varying
original coarse endpoint in the original signed fine-to-coarse geometry. -/
theorem face (G : Gauge) (P : Teller G) (L : Side) (n : ℕ) : ∃ δ N : ℝ, 0<δ ∧ 0<N ∧
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), P.Funds S T → S.patch.L=L → ∀ (s : Signed) (R : ℕ) (i : Twin f),
      Point 0 (s.act (S.ratio.parent i.1.1)) δ n (fun B => Pressure.zip (fun i j =>
        PhysicalAffineScalarUncut.faceStack T (turn s 1 B) i j-T.Φ R (turn s 1 B) i j) (fun j => value T s j B) i)
        (N*Real.exp (-(P.η/2)*((R:ℝ)/(5*(L.val:ℝ))))) := by
  obtain ⟨e,A,he,hA,hY⟩ := whole G P n
  let B5 := 5*(L.val:ℝ)
  let ξ := P.η/4
  let ν := P.η/(4*B5)
  have hB : 0<B5 := by unfold B5; have h:=L.property; positivity
  have hξ : 0<ξ := by unfold ξ; have h:=P.width; positivity
  have hν : 0<ν := div_pos P.width (mul_pos (by norm_num) hB)
  let δ := min e (min (ν/(4*((n:ℝ)+1))) (ξ/(2*((n:ℝ)+1))))
  have hδ : 0<δ := lt_min he (lt_min (div_pos hν (by positivity)) (div_pos hξ (by positivity)))
  have hh (h j : ℝ) (hh : 0<h) (hv : δ≤j/(h*((n:ℝ)+1))) : h*n*δ≤j := by
    have hd := (le_div_iff₀ (mul_pos hh (by positivity))).mp hv
    nlinarith only [hd,mul_nonneg hh.le hδ.le]
  have h1 : 2*n*δ≤ν/2 := by linarith [hh 4 ν (by norm_num) ((min_le_right ..).trans (min_le_left ..))]
  have h2 : n*δ≤ξ/2 := by linarith [hh 2 ξ (by norm_num) ((min_le_right ..).trans (min_le_right ..))]
  let a := Real.exp (4*ν+3*P.η/4)*FreeResolvent.Affine.elbow G n (ν/4)*(P.C/(L.val:ℝ)^2)
  let Z := (Fintype.card G.ColorIndex:ℝ)*a
  let M := 1+|multiplier G n Z A ξ|
  refine ⟨δ,M,hδ,by unfold M; positivity,?_⟩
  intro c f S T hP hL s R i
  let t := Real.exp (-(P.η/2)*((R:ℝ)/B5))
  let x := S.ratio.parent i.1.1
  let D (j : Twin c) (B : PriceCoords G c) := PhysicalAffineScalarUncut.faceStack T (turn s 1 B) i j-T.Φ R (turn s 1 B) i j
  have hp := transported P L n T hP hL s R i δ hδ.le h1
  have ht : 0≤t := (Real.exp_pos _).le
  have hC := Push.AbsoluteSums.budget_nonneg (hP.crosses.2.2.1 (S.ratio.residue (mesh i).1,(mesh i).2) (mesh i).2)
  rw [hL] at hC
  have hZ : 0≤Z := by unfold Z a; exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg (Real.exp_pos _).le (FreeResolvent.Affine.elbow_nn ..)) hC)
  have h := apply_rows n s x D (value T s) hδ.le hξ h2 (mul_nonneg hZ ht) hA.le hp
    (fun j => (hY S T hP s j).mono (min_le_left ..) le_rfl)
  apply h.mono le_rfl
  have hh := mul_le_mul_of_nonneg_right (show multiplier G n Z A ξ≤M by unfold M; linarith [le_abs_self (multiplier G n Z A ξ)]) ht
  rw [multiplier_smul]
  exact hh

end YM.Integration.ConditionalAffineLocalizedProduct
