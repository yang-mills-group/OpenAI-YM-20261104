import YM.Integration.WilsonMovingForkSafeProfiles

/-! The actual normalized locations of the full physical read and the reflected
Gram read fit the same real grid and separation invoice as the pointed trial. -/
noncomputable section
namespace YM.Integration.WilsonMovingForkPointHousing
open Function Filter Set Pert.Asymptotics OPE RG17
open WilsonMacroscopicRichTestGeometry WilsonMacroscopicRichMovingPlane
open OPE.Orbits OPE.Arboreal
open WilsonPublicForkIndependentPlacement
open scoped Topology

variable {G:Gauge}{n:ℕ}

def Fits (r t M η:ℝ){l:ℕ}(Y:Points l):Prop:=
  (∀i,‖r • (r⁻¹ • Y i)‖ ≤ M*t) ∧
    ∀i k,i≠k → η ≤ dist (r⁻¹ • Y i) (r⁻¹ • Y k)

private theorem scaled {r t M η:ℝ}{l:ℕ}{Y:Points l}(rp:0<r)
    (bound:∀i,‖Y i‖≤M*t)(gap:∀i k,i≠k → r*η≤‖Y i-Y k‖):Fits r t M η Y:=by
  refine ⟨fun i=>by rw [smul_inv_smul₀ rp.ne'];exact bound i,?_⟩
  intro i k ik
  rw [dist_eq_norm,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr rp),
    ←div_eq_inv_mul,le_div_iff₀ rp,mul_comm]
  exact gap i k ik

theorem boxes (K:Set (Points n))(compact:IsCompact K)(spread:K⊆conf n)(φ:Test 2):
    ∃M η δ:ℝ,0<M ∧ 0<η ∧ 0<δ ∧ ∀r t:ℝ,0<r → r≤t → r/t≤δ →
      (∀x∈K,∀z∈tsupport φ,Fits r t M η (placed r t x (relative z))) ∧
      (∀z∈tsupport φ,Fits r t M η (t • z)):=by
  obtain ⟨a,b,a0,b0,near⟩:=roomCosts compact spread
  obtain ⟨c,d,c0,d0,far⟩:=roomCosts φ.hasCompactSupport φ.tsupport_subset
  let M:=1+max a (2*c)
  let η:=min b (d/2)
  have mp:0<M:=add_pos_of_pos_of_nonneg zero_lt_one (a0.trans (le_max_left _ _))
  have ep:0<η:=lt_min b0 (half_pos d0)
  have ma:a≤M:=by dsimp[M];linarith [le_max_left a (2*c)]
  have mc:2*c≤M:=by dsimp[M];linarith [le_max_right a (2*c)]
  have eb:η≤b:=min_le_left _ _
  have ed:2*η≤d:=by linarith [min_le_right b (d/2)]
  refine ⟨M,η,η/M,mp,ep,div_pos ep mp,?_⟩
  intro r t rp rt step
  have tp:=rp.trans_le rt
  have bill:r*M≤t*η:=by have:= (div_le_div_iff₀ tp mp).mp step;linarith
  have fx(z:Points 2)(hz:z∈tsupport φ)(i:Fin 2):‖z i‖≤c:=by
    simpa [posed] using (far 1 one_pos z hz).span i
  have sep(z:Points 2)(hz:z∈tsupport φ)(i k:Fin 2)(ik:i≠k):d≤‖z i-z k‖:=by
    simpa [posed] using (far 1 one_pos z hz).spaced i k ik
  constructor
  · intro x hx z hz
    let v:=relative z 0
    have low:d≤‖v‖:=sep z hz 1 0 (by decide)
    have hi:‖v‖≤M:=by
      change ‖z 1-z 0‖≤M
      linarith [norm_sub_le (z 1) (z 0),fx z hz 1,fx z hz 0]
    have nx(i:Fin n):‖x i‖≤M:=by exact (by simpa [posed] using (near 1 one_pos x hx).span i:‖x i‖≤a).trans ma
    have join(i:Fin n):r*η≤‖r • x i-t • v‖:=by
      have line : ‖t • v‖≤‖r • x i-t • v‖+‖r • x i‖:=by
        simpa only [norm_sub_rev (t • v) (r • x i)] using norm_le_norm_sub_add (t • v) (r • x i)
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos rp,abs_of_pos tp] at line
      linarith [mul_le_mul_of_nonneg_left (nx i) rp.le,
        mul_le_mul_of_nonneg_left (ed.trans low) tp.le,mul_le_mul_of_nonneg_right rt ep.le]
    let Y:=placed r t x (relative z)
    have nearY(i:Fin n):Y (Fin.castAdd 1 i)=r•x i:=by simp [Y,placed]
    have farY(i:Fin 1):Y (Fin.natAdd n i)=t•v:=by
      have eq:i=0:=Subsingleton.elim _ _
      simp [Y,placed,v,eq]
    apply scaled rp
    · intro i
      induction i using Fin.addCases with
      | left i => rw [nearY,norm_smul,Real.norm_eq_abs,abs_of_pos rp];nlinarith [mul_le_mul_of_nonneg_left (nx i) rp.le,mul_le_mul_of_nonneg_right rt mp.le]
      | right i => rw [farY,norm_smul,Real.norm_eq_abs,abs_of_pos tp];nlinarith [mul_le_mul_of_nonneg_left hi tp.le]
    · intro i k
      induction i using Fin.addCases with
      | left i =>
        induction k using Fin.addCases with
        | left k =>
          intro ik
          have ne:i≠k:=fun eq=>ik (eq ▸ rfl)
          have diff:b≤‖x i-x k‖:=by simpa [posed] using (near 1 one_pos x hx).spaced i k ne
          rw [nearY,nearY,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos rp]
          exact mul_le_mul_of_nonneg_left (eb.trans diff) rp.le
        | right k => intro _;rw [nearY,farY];exact join i
      | right i =>
        induction k using Fin.addCases with
        | left k => intro _;rw [farY,nearY,norm_sub_rev];exact join k
        | right k => intro ne;exact (ne (congrArg (Fin.natAdd n) (Subsingleton.elim _ _))).elim
  · intro z hz
    apply scaled rp
    · intro i
      change ‖t•z i‖≤M*t
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos tp,mul_comm M]
      exact mul_le_mul_of_nonneg_left ((fx z hz i).trans (by linarith)) tp.le
    · intro i k ik
      change r*η≤‖t•z i-t•z k‖
      rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos tp]
      exact mul_le_mul rt (by linarith [sep z hz i k ik]) ep.le tp.le

end YM.Integration.WilsonMovingForkPointHousing
