import YM.Integration.WilsonMacroscopicRichTestGeometry

/-! The true joint and pair test supports have one quantitative clearance
in near units and one bounded outer radius, at every smaller scale ratio. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSampleGeometry
open Function Filter Set RG17 WilsonMacroscopicRichMovingPlane WilsonMacroscopicRichTestGeometry
open scoped Topology Classical
variable {n:ℕ}

theorem scaled {r t:ℝ}(rp:0<r)(x:Points n)(z:Points 2):
    r • placed 1 (t/r) x (relative z)=placed r t x (relative z) ∧ r • ((t/r) • z)=t • z:=by
  have cancel:r*(t/r)=t:=by field_simp
  refine ⟨?_,by rw [smul_smul,cancel]⟩
  ext1 i
  induction i using Fin.addCases <;> simp [placed,smul_smul,cancel]

theorem original (K:Set (Points n))(compact:IsCompact K)(separated:K⊆conf n)(φ:Test 2):
    ∃M:ℝ,0<M ∧ ∃η:ℝ,0<η ∧ ∃δ:ℝ,0<δ ∧ ∀r t:ℝ,0<r → r≤t → r/t≤δ → 
      ∀x∈K,∀z∈tsupport φ,
      let Y:=placed 1 (t/r) x (relative z)
      let Z:=(t/r) • z
      (∀i,‖r • Y i‖≤M*t) ∧ (∀i k,i≠k → η≤dist (Y i) (Y k)) ∧
      (∀i,‖r • Z i‖≤M*t) ∧ (∀i k,i≠k → η≤dist (Z i) (Z k)):=by
  obtain ⟨A,δA,ap,δap,nearRoom⟩:=RG17.roomCosts compact separated
  obtain ⟨B,δB,bp,δbp,farRoom⟩:=RG17.roomCosts φ.hasCompactSupport φ.tsupport_subset
  let M:=A+2*B+1
  let η:=min 1 (min δA δB)
  have mp:0<M:=by dsimp [M];linarith
  have ηp:0<η:=lt_min zero_lt_one (lt_min δap δbp)
  refine ⟨M,mp,η,ηp,δB/(A+1),div_pos δbp (by linarith),?_⟩
  intro r t rp rt ratio x hx z hz Y Z
  have tp:=rp.trans_le rt
  have scale:0≤t/r:=(div_pos tp rp).le
  have large:1≤t/r:=(one_le_div rp).mpr rt
  have near(i:Fin n):‖x i‖≤A:=by simpa [posed] using (nearRoom 1 one_pos x hx).span i
  have wide(i:Fin 2):‖z i‖≤B:=by simpa [posed] using (farRoom 1 one_pos z hz).span i
  have sep(i k:Fin n)(ne:i≠k):δA≤dist (x i) (x k):=by
    simpa [posed,dist_eq_norm] using (nearRoom 1 one_pos x hx).spaced i k ne
  have away(i k:Fin 2)(ne:i≠k):δB≤dist (z i) (z k):=by
    simpa [posed,dist_eq_norm] using (farRoom 1 one_pos z hz).spaced i k ne
  have rel(k:Fin 1):‖relative z k‖≤2*B:=by
    change ‖z k.succ-z 0‖≤2*B
    linarith [norm_sub_le (z k.succ) (z 0),wide k.succ,wide 0]
  have gap:A+1≤(t/r)*δB:=by
    have h:= (div_le_div_iff₀ tp (show 0<A+1 by linarith)).mp ratio
    rw [div_mul_eq_mul_div,le_div_iff₀ rp];nlinarith only [h]
  have cross(i:Fin n)(k:Fin 1):η≤dist (x i) ((t/r) • relative z k):=by
    have endp:δB≤‖relative z k‖:=by simpa [relative,dist_eq_norm] using away k.succ 0 (Fin.succ_ne_zero k)
    have lower:=mul_le_mul_of_nonneg_left endp scale
    have sub:=norm_sub_norm_le ((t/r) • relative z k) (x i)
    rw [norm_smul_of_nonneg scale,←dist_eq_norm,dist_comm] at sub
    exact (min_le_left _ _).trans (by linarith only [near i,gap,lower,sub])
  have cancel:r*(t/r)=t:=by field_simp
  have yr(i:Fin n):Y (Fin.castAdd 1 i)=x i:=by simp [Y,placed]
  have yf(i:Fin 1):Y (Fin.natAdd n i)=(t/r) • relative z i:=by simp [Y,placed]
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    induction i using Fin.addCases with
    | left i=>
      rw [yr,norm_smul_of_nonneg rp.le]
      exact (mul_le_mul_of_nonneg_left (near i) rp.le).trans
        ((mul_le_mul_of_nonneg_right rt (by linarith)).trans (by dsimp [M];nlinarith))
    | right k=>
      rw [yf,smul_smul,cancel,norm_smul_of_nonneg tp.le]
      calc t*‖relative z k‖≤t*(2*B):=mul_le_mul_of_nonneg_left (rel k) tp.le
           _≤M*t:=by dsimp [M];nlinarith
  · intro i k ne
    cases i using Fin.addCases <;> cases k using Fin.addCases
    · rw [yr,yr];exact (min_le_right _ _).trans ((min_le_left _ _).trans (sep _ _ (fun eq=>ne (congrArg _ eq))))
    · rw [yr,yf];exact cross _ _
    · rw [yf,yr,dist_comm];exact cross _ _
    · exact (ne (congrArg _ (Subsingleton.elim _ _))).elim
  · intro i
    change ‖r • ((t/r) • z i)‖≤M*t
    rw [smul_smul,cancel,norm_smul_of_nonneg tp.le]
    calc t*‖z i‖≤t*B:=mul_le_mul_of_nonneg_left (wide i) tp.le
         _≤M*t:=by dsimp [M];nlinarith
  · intro i k ne
    change η≤dist ((t/r) • z i) ((t/r) • z k)
    rw [dist_eq_norm,←smul_sub,norm_smul_of_nonneg scale,←dist_eq_norm]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((away i k ne).trans (le_mul_of_one_le_left (dist_nonneg) large)))

end YM.Integration.WilsonMovingForkSampleGeometry
end
