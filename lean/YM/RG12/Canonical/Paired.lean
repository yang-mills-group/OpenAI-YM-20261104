import YM.RG12.Canonical.Conclude
import YM.RG12.Frames.Stability

/-!
# Enough: initial reflected-two-point physical estimates (conditional)

Testing at a discrete set is sufficient. For specifying a finite-geometry development target
we give **one** option: finite reflected pairs on one coordinate axis, upper slot linear in the
field and lower antilinear (useAt with S.adj precision); optionally sum such tests, possibly
polarizing them in positions. Don't confuse with a conclusion that the necessary coercivity is
achievable by every point reflection matrix. If point testing is too demanding, all the survey
machinery applies to any sesquilinear measurements, e.g. smeared on separated compact
profile geometry, by plugging them in place of `sampleForm`. Likewise those can use derivative
detectors on insertions (finite deriv demand and normalized accordingly). This section doesn't
identify predictions in different gauges or regulators. It reduces actual MatrixTicket to
estimates still to be proved on actual S; estimates on a free construction enter only via
`nonsingular` if provided. All tests used here are UNSELECTED. Reader result at end retains
exact scope of supplied `OPE.tickets_suffice` (not restricted to unselected).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Desk.Paired
open Function Filter Finset Lattice RG Source Frames Table OPE Gram
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {S : Table C.book} (B : DiffPlan S)
  {M : ∀ d, ℕ → RepChart C d} {phi : Extraction.Order}
  (U : Spec.Final C phi S)

-- convenient orientation in curry

def gramEntry (d:ℕ) (x:Points 2) (t:Axis) : Gram.Sesqui (S.Field d) :=
    let J:= S.classMoment S (fun _=>d) x
    let Q : S.Field d →ₗ[ℂ] (S.Field d →ₗ[ℂ] ℂ):= {
      toFun a := (MultilinearMap.ofSubsingleton ℂ (S.Field d) ℂ (0:Fin 1)).symm (J.curryLeft a)
      map_add' a b := by
        apply LinearMap.ext; intro q
        change J.curryLeft _ (fun _=> q) = (J.curryLeft a (fun _=> q))+ (J.curryLeft b (fun _=> q))
        rw [map_add,_root_.add_apply]
      map_smul' c a := by
        apply LinearMap.ext; intro q
        change J.curryLeft _ (fun _=> q) = c • (J.curryLeft a (fun _=> q))
        rw [map_smul,_root_.smul_apply] }
    Q.compl₂ (S.adj U.room.kernel.spin d t)

def arrangement (a:Axis)(x y:E4): Points 2:= points ![x,Ortho.move (Signed.reflect a) y]

lemma clear (a:Axis)(x y:E4)(hx:0 < x a)(hy:0 < y a): arrangement a x y ∈ conf 2:= by
  intro i j hij
  by_contra h
  fin_cases i <;> fin_cases j
  · exact h rfl
  · have hh:x=Ortho.move (Signed.reflect a) y:=hij
    have he:= congr_arg (fun x:E4=> x a) hh; simp [Signed.mirrored] at he; linarith
  · have hh:x=Ortho.move (Signed.reflect a) y:=hij.symm
    have he:= congr_arg (fun x:E4=>x a) hh; simp [Signed.mirrored] at he; linarith
  exact h rfl

lemma formula (d:ℕ) (x:Points 2) (a:Axis)(v w:S.Field d):
    gramEntry U d x a v w=S.useAt S x ![(⟨d,v⟩:S.Tag),⟨d,S.adj U.room.kernel.spin d a w⟩]:=by
  change (S.classMoment S (fun _=>d) x) (Fin.cons v (fun _:Fin 1=> S.adj U.room.kernel.spin d a w))=_
  -- dependent equality
  change _=(S.classMoment S (fun i=> (![_,_] i:S.Tag).1) x) _
  let f : Fin 2→S.Tag:=fun i=> ⟨d, Fin.cons v (α:=fun _=> S.Field d) (fun _=>S.adj U.room.kernel.spin d a w) i⟩
  rw [show ![(⟨d,v⟩:S.Tag),⟨d,S.adj U.room.kernel.spin d a w⟩] = f from (by funext i; fin_cases i<;>rfl)]

structure Scope (n : ℕ) where
  weight : Fin n → ℂ
  axis : Fin n → Axis
  incoming : Fin n → E4
  reflecting : Fin n → E4
  ahead i : 0 < incoming i (axis i)
  stays i : 0 < reflecting i (axis i)

def configs {n} (D:Scope n)(t:ℝ)(i:Fin n): Points 2:= arrangement (D.axis i) (t • D.incoming i) (t • D.reflecting i)
lemma fits {n} (D:Scope n){t:ℝ}(h:0<t)(i:Fin n): configs D t i∈ conf 2:=
    Paired.clear _ _ _ (by change 0<t*_; exact mul_pos h (D.ahead i)) (by change 0<t*_; exact mul_pos h (D.stays i))

def sampleForm {n} (D:Scope n)(d:ℕ)(t:ℝ) : Gram.Square (S.Field d):= Gram.fromSesqui (∑ i,D.weight i • gramEntry U d (configs D t i) (D.axis i))
lemma samples_here {n} (D:Scope n)(d:ℕ)(t:ℝ)(x:S.Field d) :
    (sampleForm U D d t).eval x =
      (∑ i,D.weight i * S.useAt S (configs D t i) ![(⟨d,x⟩:S.Tag),⟨d,S.adj U.room.kernel.spin d (D.axis i) x⟩]).re:=by
    unfold sampleForm Gram.fromSesqui
    dsimp only
    simp only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,formula]


local notation "B0"=> U.sector.derivatives
local notation "S!"=> Sample.age

structure Elementary (P:Prescription B0)(hp:P.Coherent)(M:∀ d:ℕ,ℕ → RepChart C d)(d:ℕ) (n:ℕ)(Q:Scope n)
    (Y:ℕ → Frames.Col (Sector B0 d) →ₗ[ℂ] S.Field d)
    (Z:ℕ → Frames.Col (Sector B0 d) →ₗ[ℂ] C.label d)
    (J:ℕ → Frames.Col (Sector B0 d) ≃ₗ[ℂ] Frames.Col (Sector B0 d))
    (G:Frames.Col (Sector B0 d)→ ℝ)(K a:ℝ)(p b e:ℕ) : Prop where
  zero_lead : 1 ≤ K
  regular (x): G x ≤ K * ‖x‖^2 ∧ ‖x‖^2 ≤ K * G x
  fits_age : 0 ≤ a ∧ a*(2*K) ≤ p
  pivots : ∀ᶠ i:ℕ in atTop, ∀ x:Frames.Col (Sector B0 d),
    |(sampleForm U Q d (Sample.length i)).eval (Y i x)-G x| ≤ (2*K)⁻¹ * ‖x‖^2
  placement : ∀ᶠ i in atTop, Frames.triangular _ ((official P hp d).symm.toLinearMap.comp (Y i))
  adjusts : ∀ᶠ i in atTop, Frames.triangular _ (J i).toLinearMap∧ ∀ j x, Frames.block _ (J i).toLinearMap j j x=x
  table : ∀ᶠ i in atTop,∀ x,‖J i x‖ ≤ (S! i)^b*‖x‖ ∧ ‖(J i).symm x‖ ≤ (S! i)^b*‖x‖
  across : ∀ᶠ i:ℕ in atTop, ∀ x:Frames.Col (Sector B0 d),
    let D:=(sampleForm U Q d (Sample.length i)).eval; let V:=(sampleForm U Q d (Sample.length (i+1))).eval
    |D (Y (i+1) (Frames.dilate (Sample.ratio i) (J i x))) - V (Y (i+1) x)| ≤ a/(S! i)*‖x‖^2
  reads : ∀ᶠ k in atTop,
    let n := Sample.atMesh C k; let gamma := (sampleForm U Q d (Sample.length n)).eval
    let V:= engineering (S:=S) M d k; let v := C.path.levels.clock.hatBeta k^e
    (∀ x:C.label d,gamma (V x) ≤ (v * mass C d x)^2) ∧
    (∀ x:Col (Sector B0 d),mass C d (Z k x) ≤ v*‖x‖ ∧ ‖x‖^2 ≤ v^2 * gamma (V (Z k x)))

theorem useTest (hG:G.Simple) (P:Prescription B0)(hp:P.Coherent)(M:∀d:ℕ,ℕ→ RepChart C d) (d:ℕ){n:ℕ}{D:Scope n}
    {Y:ℕ → Frames.Col (Sector B0 d) →ₗ[ℂ] S.Field d} {Z:ℕ → Frames.Col (Sector B0 d) →ₗ[ℂ] C.label d}
    {J:ℕ → Frames.Col (Sector B0 d) ≃ₗ[ℂ] Frames.Col (Sector B0 d)} {H:Frames.Col (Sector B0 d)→ℝ} {K a:ℝ} {p b e:ℕ}
    (h: Elementary U P hp M d n D Y Z J H K a p b e) : FramesInput B0 P hp M d:=by
   have hK:= h.zero_lead; have ha:Tendsto Sample.age atTop atTop:=by unfold Sample.age; exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
   obtain ⟨i,hi⟩:= Sample.samples_clock (K:=2*K)
   obtain ⟨s,hs⟩:= eventually_atTop.mp ( h.adjusts.and (h.table.and (h.across.and (h.pivots.and (h.placement.and
      ((eventually_ge_atTop i).and (ha.eventually_ge_atTop (2*p))))))))
   let R i:= Real.sqrt ∘ (sampleForm U D d (Sample.length i)).eval
   refine ⟨Y,R,J,2*K,2*p,b,s,?_,Z,e,?_ ⟩
   · have hz n (he:s≤n):= Gram.nonsingular H hK h.regular ((hs n he).2.2.2.1)
     refine ⟨fun i _=> Sample.samples_spacing i,fun k he=>hi k (hs k he).2.2.2.2.2.1,fun k he=>(hs k he).2.2.2.2.1,fun k he=> Gram.stable (hz _ he),fun k he=>(hs k he).1,fun k he=>(hs k he).2.1,fun k he x=> ?_⟩
     have ht:=hs k he; have hN:=hi k ht.2.2.2.2.2.1; have hw:(1:ℝ)≤ S! k:= by unfold Sample.age; linarith only [Nat.cast_nonneg (α:=ℝ) k]
     apply Gram.step_ratio (X:= fun x: Col (Sector B0 d)=>Y (k+1) (Frames.dilate (Sample.ratio k) (J k x))) (P:=sampleForm U D d (Sample.length k)) (hz _ (he.trans k.le_succ)) hw _ h.fits_age.2 ht.2.2.2.2.2.2 h.fits_age.1 ht.2.2.1
     rw [le_div_iff₀ (zero_lt_one.trans_le hw), add_mul,one_mul,inv_mul_cancel₀ (ne_of_gt (zero_lt_one.trans_le hw))]; exact hN.2.1
   filter_upwards [h.reads,(hat_grows (C:=C) hG).eventually_ge_atTop 1] with k hk hh
   let V:= Z k; let q:= C.path.levels.clock.hatBeta k; let gamma:= (sampleForm U D d (Sample.length (Sample.atMesh C k))).eval
   have h0:0< q^e:=pow_pos (zero_lt_one.trans_le hh) _
   have hS:q^e ≤ q^(e+2):=pow_le_pow_right₀ hh (by omega)
   refine ⟨fun x=> ?_,fun x=> ((hk.2 x).1.trans (mul_le_mul_of_nonneg_right hS (norm_nonneg _))),fun x=> ?_⟩
   · change Real.sqrt (gamma _) ≤ q^(e+2)*_
     exact ((Real.sqrt_le_sqrt (hk.1 x)).trans_eq (Real.sqrt_sq (mul_nonneg h0.le (mass_nonneg ..)))).trans (mul_le_mul_of_nonneg_right hS (mass_nonneg ..))
   change _≤q^(e+2)*Real.sqrt (gamma _)
   have hf:0 ≤ gamma (engineering (S:=S) M d k (V x)):= nonneg_of_mul_nonneg_right ((sq_nonneg _).trans (hk.2 x).2) (pow_pos h0 _)
   apply le_trans _ (mul_le_mul_of_nonneg_right hS (Real.sqrt_nonneg _)); apply le_of_pow_le_pow_left₀ (n:=2) (by norm_num) (mul_nonneg h0.le (Real.sqrt_nonneg _))
   rw [mul_pow, Real.sq_sqrt hf]; exact (hk.2 x).2
end YM.RG12.Desk.Paired
