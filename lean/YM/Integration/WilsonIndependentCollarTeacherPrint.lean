import YM.Integration.WilsonIndependentCollarOpticalElected
import YM.Integration.WilsonIndependentCollarOpticalPrint

/-! The selected teacher reads the canonical compiler at the connected
front. The remaining exponential pays the relative positions of that face. -/
set_option autoImplicit false
set_option maxHeartbeats 270000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarTeacherPrint
open Function Finset Lattice RG Precision Wilson Exterior Work.F08
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Flooring
open WilsonIndependentCollarPrintIncome
open scoped BigOperators Classical
variable {G:Gauge} {ι:Type} {E:Type}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem original (I:Gear G)(σ:ℝ)(pos:0<σ)(paid:I.s=2*σ)(widths:Widths G)
    (k p h:ℕ)(hp:h≤p)(P:Era G E)(auth:Auth k P)(S:Finset ι)(y:ι → Cover)(v:ι)(root:v∈S)
    (A:ℝ)(honest:0≤A)(fund:∀i<p,∀r,Wig Bank.terrain y σ A S (P.2 i r))
    (t:ℝ)(slot:0<t)(reach:8*t*S.card≤3*σ)(narrow:t≤(issue widths p k I).strip):
    let packet:=sphere P k h v y
    let C:=(issue widths p k I).fee*A
    Rains packet h t (C*Real.exp (-σ/2*realmSize S y)) ∧
      tenure packet S y v h t (Real.exp (3*σ/8)*C*Real.exp (-σ/8*realmSize S y)) ∧
      ∀j<h,let filed:=shifted (baton packet h) (y v)
        Auth k filed ∧ filed.2 j=P.2 j ∧ ∀ n r,filed.1 n j r=Carp.plume (P.2 j r) n:=by
  intro packet C
  let Q:=shifted P (-y v)
  let b:=realmSize S y
  let a:=A*Real.exp (-σ/2*b)
  have credit:0≤a:=mul_nonneg honest (Real.exp_pos _).le
  have native:Rain Q.2 p (σ/2) a:=⟨credit,fun i hi r=>skyRoot _ y (fund i hi r) root pos⟩
  have inlet:strip widths p k I≤σ/2:=by
    apply (min_le_right ..).trans;apply (min_le_left ..).trans
    rw [paid];linarith
  let out:=issue widths p k I
  obtain ⟨legs,exactJet⟩:=out.stencil h hp E Q.2 a (nimb Q (auth.shifted _) p)
    (native.less _ inlet le_rfl)
  have wage:out.fee*a=C*Real.exp (-σ/2*b):=by dsimp [C,a,out];ring
  rw [wage] at legs
  have filed:Rains packet h t (C*Real.exp (-σ/2*b)):=legs.slack narrow le_rfl
  refine ⟨filed,?_,?_⟩
  · intro j hj rk
    let z:=feeH y v S
    apply cap_raise (cap_scale (filed.2 j hj|>.2 rk).2 (show 0≤Real.exp (t*z) by positivity))
    have lower:0≤C:=mul_nonneg (zero_le_one.trans out.funded) honest
    have front:(z:ℝ)≤(S.card:ℝ)*(1+b):=by exact_mod_cast feeH_le y root
    have tb:t*(z:ℝ)≤3*σ/8*(1+(b:ℝ)):=by
      calc _ ≤ t*((S.card:ℝ)*(1+b)):=mul_le_mul_of_nonneg_left front slot.le
           _ = (t*(S.card:ℝ))*(1+b):=by ring
           _ ≤ _:=mul_le_mul_of_nonneg_right (by linarith only [reach]) (by positivity)
    calc
      _ = C*(Real.exp (t*z)*Real.exp (-σ/2*b)):=by ring
      _ ≤ C*(Real.exp (3*σ/8)*Real.exp (-σ/8*b)):=by
        apply mul_le_mul_of_nonneg_left _ lower
        rw [←Real.exp_add,←Real.exp_add,Real.exp_le_exp];linarith only [tb]
      _ = _:=by dsimp [b];ring
  · intro j hj
    obtain ⟨exactCover,exactFold⟩:=shineZ P y filed slot exactJet j hj
    exact ⟨(root_robe packet filed slot (y v)).1,exactCover,exactFold⟩

end YM.Integration.WilsonIndependentCollarTeacherPrint
end
