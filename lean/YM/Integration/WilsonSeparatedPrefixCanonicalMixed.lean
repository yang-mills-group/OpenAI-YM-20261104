import YM.Integration.WilsonAddressedPublicGridRoster
import YM.Integration.WilsonCapturedPrimaryWardCarton
import YM.Integration.WilsonPrecontactSeparatedLamps
import YM.MergeProof.Stretch

/-! An original measured Carton can be tapped at its reporting date. Every mixed
entry is supported on its own occupied anchors, including a mixed hard box. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalMixed
open Function Finset Set MeasureTheory Lattice Wilson RG Marker MergeProof Accent
open Push.GridApprox.Nil Ac
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {V I Y:Type} [DecidableEq V] {C:Census V}
  {o:V→Site n} {B:ℕ} {t:ℝ}

theorem extent {Z:Support n} {f:Config G n→Poly C} (record:Borne o Z f t)
    (modes:∀U,rises (f U)) (hB:5≤B)
    (apart:∀v u:V,v≠u → B^2+1 ≤ separation (o v) (o u))
    {U:Config G n} (live:f U≠0) : B/8 ≤ coverNumber B Z := by
  classical
  obtain ⟨s,hit⟩:∃s:C.Mode,(f U).part s≠0:=by
    by_contra! empty
    apply live
    ext1 i
    exact empty i
  obtain ⟨v,hv,u,hu,diff⟩ := one_lt_card.mp (show 1<s.val.card from modes _ _ hit)
  have inside:((s.val:Set V)⊆{a|o a∈Z}):=by
    by_contra bad
    exact hit (record.scope U s bad)
  have distance := (apart v u diff).trans (Corona.extent Z B (inside hv) (inside hu))
  have d := Nat.div_mul_le_self B 8
  have e := Nat.mul_le_mul_right B d
  have f := Nat.mul_le_mul_right B hB
  have h4:4*(B/8)≤B:=by omega
  have : (B/8)*(4*B+2)+2*B ≤ B^2+1:=by nlinarith only [e,f,h4]
  exact Nat.le_of_mul_le_mul_right (Nat.le_of_add_le_add_right (this.trans distance)) (by omega)

theorem loci {w:V→ℝ} {F:Y→Poly C} {a:ℝ} (ordinary:Loci w F a) (z:ℂ) :
    Loci w (fun U=>z • F U) (‖z‖*a):=by
  obtain ⟨v,positive,bound,price⟩:=ordinary
  refine ⟨fun s=>‖z‖*v s,fun s=>mul_nonneg (norm_nonneg _) (positive s),fun U s=>?_,?_⟩
  · simpa only [Poly.part_smul,norm_mul] using mul_le_mul_of_nonneg_left (bound U s) (norm_nonneg z)
  · unfold wordsPrice at *
    calc
      _ = ‖z‖*∑s,Poly.toll w s*v s:=by rw [Finset.mul_sum];apply sum_congr rfl;intro;simp [mul_left_comm]
      _ ≤ _:=mul_le_mul_of_nonneg_left price (norm_nonneg _)

theorem salary [Finite I] {w:V→ℝ} {S:I→Support n} {F:I → Config G n→Poly C}
    {e δ a:ℝ} (δ₀:0≤δ) (w₀:∀v,0<w v) (hB:5≤B)
    (apart:∀v u:V,v≠u → B^2+1 ≤ separation (o v) (o u))
    (record:∀i,Borne o (S i) (F i) t) (modes:∀i U,rises (F i U))
    (stock:Towed w S F B (e+δ) a) (z:ℂ) (allow:‖z‖≤Real.exp (δ*(B/8:ℕ))):
    Towed w S (fun i U=>z • F i U) B e a := by
  classical
  letI:=Fintype.ofFinite I
  obtain ⟨raw,_,cash,rate⟩:=stock
  let fee (i:I):ℝ:=if B/8 ≤ coverNumber B (S i) then ‖z‖*raw i else 0
  have nonneg(i:I):0≤raw i:=((rate i).fares w₀).1
  refine ⟨fee,Summable.of_finite,fun x=>Extra.Multi.Budget.mono (cash x) (fun i=>?_) (fun i=>?_) le_rfl,fun i=>?_⟩
  · dsimp only [fee]
    have pos:=nonneg i
    split_ifs <;> positivity
  · by_cases belongs:x∈S i
    · simp only [belongs,if_true,fee]
      split
      · rename_i long
        calc
          _ ≤ Real.exp (δ*(coverNumber B (S i):ℝ))*raw i*Real.exp (e*↑(coverNumber B (S i))):=by
                exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (allow.trans (Real.exp_monotone
                  (mul_le_mul_of_nonneg_left (by exact_mod_cast long) δ₀))) (nonneg i)) (Real.exp_pos _).le
          _ = _:=by rw [add_mul,Real.exp_add];ring
      · simp only [zero_mul];exact mul_nonneg (nonneg i) (Real.exp_pos _).le
    · simp [belongs]
  · by_cases long:B/8 ≤ coverNumber B (S i)
    · simpa only [fee,long,if_true] using loci (rate i) z
    · have vanish (U):F i U=0:=by
        by_contra occurs
        exact long (extent (record i) (modes i) hB apart occurs)
      refine ⟨0,le_refl _,fun U s=>by simp [vanish],?_⟩
      simp [fee,long,wordsPrice]

end YM.Integration.WilsonSeparatedPrefixCanonicalMixed
end
