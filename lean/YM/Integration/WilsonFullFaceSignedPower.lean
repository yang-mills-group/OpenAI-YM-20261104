import YM.Integration.WilsonFullFaceSignedHalo

/-! A fixed inverse-coupling exponent for a signed three-seat capture. Only
the multiplicative stage constant can depend on the working Taylor order. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonFullFaceSignedPower
open Finset RG Wilson Lattice Source Labels Marker Multi QuadraticLocal Ac Push.Local Planned.GuardedAtom Extra.Histories
open WilsonFullFaceSignedHalo WilsonCapturedPrimarySoftPartition WilsonCapturedPrimarySoftMount WilsonCenteredLampCapture
open WilsonCenteredFiledAtoms WilsonThermometerCenteredAlgebra
open scoped Classical BigOperators
variable {G : Gauge} {d : ℕ} {F : Frame G d} {n : Side}
local notation "J" => Stock.census (Fin 3)

theorem bounded : ∃ B:ℝ,0≤B ∧ ∀e∈Set.Icc (0:ℝ) 1,WilsonFullFaceSignedRegular.factor e≤B :=by
  have fc : Continuous WilsonFullFaceSignedRegular.factor :=by
    unfold WilsonFullFaceSignedRegular.factor
    apply continuous_finsetSum
    intro j _
    fin_cases j <;> simp [WilsonFullFaceSignedInterpolation.coins] <;> fun_prop
  obtain ⟨b,hi⟩ : BddAbove (WilsonFullFaceSignedRegular.factor '' Set.Icc (0:ℝ) 1) :=
    isCompact_Icc.bddAbove_image fc.continuousOn
  exact ⟨max 0 b,le_max_left ..,fun e he=>(hi ⟨e,he,rfl⟩).trans (le_max_right ..)⟩

def inter : ℝ :=bounded.choose

theorem regular (p : BudgetPoint) (S : SectionData F) (Y : Hol G) (w : Fin 3→ℝ) (hw : ∀j,0<w j) (s : (J).Mode)
    (y : Site n) (Z : Support n) (housed : Z⊆halo p.B {y}) (rad : ℕ) (radius : rad≤p.B)
    {α C e K v κ μ x : ℝ} (strength : p.supportExponent≤α) (cpos : 0≤C) (ep : 0≤e) (es : e≤1)
    (one : 1≤K) (hx : 1≤x) (cap : C+3≤K*x^17) (div : 0<κ) (hv : 0≤v)
    (room : hitWidth p*v/κ≤1) (motion : WilsonReportRetainedAnchor.reprice p p.B≤2*x^2) (μ0 : 0≤μ) (rd : μ≤4*x^2) :
    Poly.toll w s*WilsonFullFaceSignedRegular.fee p Z w C e rad S Y μ v κ s ≤
      e*inter*(WilsonPlantedOrdinaryHalo.master S Y α K*x^61) :=by
  let h:=hitWidth p*v/κ
  let f:=factor Y S p.supportExponent μ
  have h0 : 0≤h:=div_nonneg (mul_nonneg (by unfold hitWidth;positivity) hv) div.le
  have f0 : 0≤f:=by
    dsimp only [f,factor,atomPrice]
    have zero:=zero_le_one.trans (readPrice_pos Y F)
    positivity
  have insert : WilsonCapturedPrimarySoftMount.fare p Z w (C+3) rad S Y μ v κ s ≤
      WilsonPlantedOrdinary.fare p Z w (C+3) 0 rad S Y μ v κ s :=by
    apply sum_le_sum
    intro q _
    have pure : 0≤tariff p Z w (0:ℝ) q :=mul_nonneg (Real.exp_nonneg _) <| prod_nonneg fun j _=>
      mul_nonneg (inv_nonneg.mpr (Poly.worth hw _).le) le_rfl
    change f*_+((0+h*_)+h*(f*_)) ≤ f*(_+_)+((0+h*(_+_))+h*(f*(_+_)))
    nlinarith only [mul_nonneg f0 pure,mul_nonneg h0 pure,mul_nonneg h0 (mul_nonneg f0 pure)]
  have supplement q (hq:q∈shards (J) s) :=WilsonPlantedOrdinaryPrice.partition p Z rad w hw s q hq
    (show 0≤C+3 by linarith only [cpos]) (D:=0) (by norm_num) cap
    (mul_nonneg (zero_le_one.trans one) (pow_nonneg (zero_le_one.trans hx) _))
  have test:=(mul_le_mul_of_nonneg_left insert (Poly.worth hw _).le).trans
    (WilsonPlantedOrdinaryHalo.original p S Y Z y w s rad hx radius housed strength div hv room motion μ0 rd one supplement)
  have scaled : e*WilsonFullFaceSignedRegular.factor e ≤ e*inter :=
    mul_le_mul_of_nonneg_left (bounded.choose_spec.2 e ⟨ep,es⟩) ep
  have ef0 : 0≤e*WilsonFullFaceSignedRegular.factor e :=mul_nonneg ep (sum_nonneg fun _ _=>norm_nonneg _)
  have m0:0≤WilsonPlantedOrdinaryHalo.master S Y α K*x^61 := by
    unfold WilsonPlantedOrdinaryHalo.master
    have kp:=zero_le_one.trans one
    have xp:=zero_le_one.trans hx
    positivity
  calc
    _ = (e*WilsonFullFaceSignedRegular.factor e)*(Poly.toll w s*WilsonCapturedPrimarySoftMount.fare p Z w (C+3) rad S Y μ v κ s) :=by
      unfold WilsonFullFaceSignedRegular.fee;ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left test ef0).trans (mul_le_mul_of_nonneg_right scaled m0)

def constants (S : SectionData F) (Y : Hol G) (α K : ℝ) :=
  let b:=roof α K
  ((Fintype.card ((J).Mode×(J).Mode):ℝ)*64^3*(2*b*(3*Real.exp 3))+
    inter*(WilsonPlantedOrdinaryHalo.master S Y α K))+2*b

theorem face (p : BudgetPoint) (S : SectionData F) (Y : Hol G) (w : Fin 3→ℝ) (hw : ∀j,0<w j) (s : (J).Mode)
    (y : Site n) (Z : Support n) (housed : Z⊆halo p.B {y}) (rad : ℕ) (radius : rad≤p.B)
    {α C e D K E ε v κ μ x shrink : ℝ} (strength : p.supportExponent≤α)
    (one : 1≤K) (hx : 1≤x) (cpos : 0≤C) (dp : 0≤D) (ep : 0≤e) (es : e≤1) (gp : 0≤E)
    (cap : C+3≤K*x^17) (dc : D≤K*x^17) (ec : E≤K*x^17)
    (lp : 1 ≤ shrink) (radiusPrice : shrink≤64*x^12) (hp : 0≤ε) (soft : ε≤1) (div : 0<κ) (hv : 0≤v)
    (rm : hitWidth p*v≤1) (room : hitWidth p*v/κ≤1)
    (motion : WilsonReportRetainedAnchor.reprice p p.B≤2*x^2) (μ0 : 0≤μ) (rd : μ≤4*x^2) :
    Poly.toll w s*WilsonFullFaceSignedCapture.fare p S Y Z w (fun j=>w j/shrink) s rad C e D ε E v κ μ ≤
      constants S Y α K*x^87*(e+ε/κ+hitWidth p*v/κ) :=by
  let b:=roof α K
  let M:=WilsonPlantedOrdinaryHalo.master S Y α K
  let N:ℝ:=Fintype.card ((J).Mode×(J).Mode)
  let h:=hitWidth p*v/κ
  let weak:=fun j=>w j/shrink
  have x0:=zero_le_one.trans hx
  have k0:=zero_le_one.trans one
  have lpos:=zero_lt_one.trans_le lp
  have ws : ∀j,0<weak j:=fun j=>div_pos (hw j) lpos
  have re : Poly.toll w s=shrink^s.val.card*Poly.toll weak s :=by
    unfold Poly.toll
    dsimp only [weak]
    rw [prod_div_distrib,prod_const]
    field_simp [lpos.ne']
  have shrinkpow : shrink^s.val.card≤64^3*x^36 :=by
    have count:s.val.card≤3:=by simpa using card_le_univ s.val
    calc _ ≤ shrink^3 := pow_le_pow_right₀ lp count
         _ ≤ (64*x^12)^3 := pow_le_pow_left₀ lpos.le radiusPrice _
         _ = _ := by rw [mul_pow,←pow_mul]
  have roofpow : roof α (K*x^17)=b*x^51 :=by dsimp [roof,b];rw [mul_pow,←pow_mul];ring
  have grown:=one_le_mul_of_one_le_of_one_le one (one_le_pow₀ hx (n:=17))
  have b0 : 0≤b:=by dsimp [b,roof];positivity
  have m0:0≤M:=by dsimp [M,WilsonPlantedOrdinaryHalo.master];positivity
  have n0 : 0≤N:=Nat.cast_nonneg _
  have i0 : 0 ≤ inter:=bounded.choose_spec.1
  have h0 : 0≤h:=div_nonneg (mul_nonneg (by unfold hitWidth;positivity) hv) div.le
  have eps0:=div_nonneg hp div.le
  have hline:=WilsonFullFaceSignedHalo.hard p weak ws s y Z housed strength gp ec grown hv div rm hp soft
  have mline:=WilsonFullFaceSignedHalo.slips p w hw s y Z housed strength cpos dp (by linarith only [cap]) dc grown hv div
  have rline:=regular p S Y w hw s y Z housed rad radius strength cpos ep es one hx cap div hv room motion μ0 rd
  rw [roofpow] at hline mline
  have charge : Poly.toll w s*WilsonFullFaceSignedHard.fee p Z weak s E ε v κ ≤
      (N*64^3*(2*b*(3*Real.exp 3)))*x^87*(ε/κ) :=by
    rw [re,mul_assoc]
    apply (mul_le_mul_of_nonneg_left hline (pow_nonneg lpos.le _)).trans
    calc
      _ ≤ (64^3*x^36)*(N*(2*(b*x^51)*(3*Real.exp 3)*(ε/κ))) := mul_le_mul_of_nonneg_right shrinkpow (by positivity)
      _ = _ :=by ring
  have shift : h*(2*(b*x^51)) ≤ (2*b)*x^87*h :=by
    have big : x^51≤x^87:=pow_le_pow_right₀ hx (by norm_num)
    exact (by ring_nf;gcongr : h*(2*(b*x^51))≤(2*b)*x^87*h)
  have localSize : e*inter*(M*x^61)≤(inter*M)*x^87*e :=by
    have big : x^61≤x^87:=pow_le_pow_right₀ hx (by norm_num)
    calc _ = ((inter*M)*e)*x^61:=by ring
         _ ≤ ((inter*M)*e)*x^87:=mul_le_mul_of_nonneg_left big (mul_nonneg (mul_nonneg i0 m0) ep)
         _ = _:=by ring
  unfold WilsonFullFaceSignedCapture.fare
  rw [mul_add,mul_add]
  apply (add_le_add (add_le_add charge (rline.trans localSize)) (mline.trans shift)).trans
  change _ ≤ ((N*64^3*(2*b*(3*Real.exp 3))+inter*M)+2*b)*x^87*(e+ε/κ+h)
  have a0 : 0≤N*64^3*(2*b*(3*Real.exp 3)):=by positivity
  have c0 : 0 ≤ inter*M:=by positivity
  have f0 : 0≤2*b:=by positivity
  let A:=N*64^3*(2*b*(3*Real.exp 3))
  let B:=inter*M
  let C':=2*b
  change A*x^87*(ε/κ)+B*x^87*e+C'*x^87*h≤(A+B+C')*x^87*(e+ε/κ+h)
  have xp : 0≤x^87:=pow_nonneg x0 _
  let common := e+ε/κ+h
  calc
    _ ≤ A*x^87*common+B*x^87*common+C'*x^87*common := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left (by dsimp [common];linarith only [ep,h0]) (mul_nonneg a0 xp))
        (mul_le_mul_of_nonneg_left (by dsimp [common];linarith only [eps0,h0]) (mul_nonneg c0 xp)))
      (mul_le_mul_of_nonneg_left (by dsimp [common];linarith only [ep,eps0]) (mul_nonneg f0 xp))
    _ = _:=by dsimp only [common];ring

end YM.Integration.WilsonFullFaceSignedPower
