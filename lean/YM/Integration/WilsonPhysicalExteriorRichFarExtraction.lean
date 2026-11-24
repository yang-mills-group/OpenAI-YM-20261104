import YM.Integration.WilsonPhysicalExteriorRichFarReturn
import YM.Integration.WilsonPhysicalExteriorReturnedDetector
import YM.Integration.WilsonPhysicalExteriorPresoldRun

/-! Presold, signed all-arity finite-cutoff residual after the *original
finite Wilson detector's own* inverse, before the periods, independent field
readers, and their test functions are presented. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorRichFarExtraction
open Function Filter Set Finset Real MeasureTheory Lattice RG RG16 Pert Pert.Position
open XSpace XSpace.Cirrus FVA2 FVA2.Register MS MS.Land MS.Menus MS.Rake MS.Tone
open PhysicalNext.Repeat.Legato WilsonPhysicalExteriorActualSides WilsonPhysicalExteriorTestedDetector
open WilsonPhysicalExteriorIssuedWord WilsonPhysicalExteriorFormalGram
open WilsonPhysicalExteriorPresoldRun PowerSeries Extra.FD
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
variable (Q:Prescription (Press.portDeck G)) (H:ℕ)
local notation "B₀" => Press.portDeck G
local notation "I" => Glyph B₀ H
local notation "Λ" => RG16.Lambda R.family.path.levels
local notation "T₀" => WilsonPhysicalExteriorFirstCutScale.ratio R

def extraction (g:Test 2) {n:ℕ} (p:Fin n→Label B₀) (D:Design n) (c c' μ:ℝ)
    (α eps:Fin (n+1)→ℝ) (u far:Fin (n+1)→Bool) (abs side:Bool) (k j per:ℕ) (f:I→Test (n+1)) (b:I) : ℂ:=
  let V:=WilsonPhysicalExteriorRichFarReturn.returned R Q H g c c' side (fun _=>μ) (j,per)
  ∑r∈antidiagonal k,∑a:I,reader R M Q p D c c' μ α eps u far abs side r.2 j per f a*coeff r.1 (V a b)

def Direct (g:Test 2) : Prop:=
  ∀(n:ℕ)(p:Fin n→Label B₀)(D:Design n)(c c':ℝ),
    (∀m,((R.family.S.block m).val:ℝ)≤log (Λ m))→1<c'→c'<c→c<2→
    ∀(lo:ℕ→ℕ)(μ:ℝ)(α:Fin (n+1)→ℝ)(q:ℝ)(k:ℕ),
    ∀ᶠ j:ℕ in atTop,∀u far:Fin (n+1)→Bool,∀abs side:Bool,∀per≥WilsonPhysicalExteriorActualSides.floor R c lo j,
    ∀eps:Fin (n+1)→ℝ,(∀i,exp (-WilsonPhysicalExteriorActualSides.time R c j)/T₀ c' j≤eps i)→
    ∀f:I→Test (n+1),(∀a,tsupport (f a)⊆D.K)→(∀a,(∫z,‖f a z‖)≤1)→∀b:I,
    ‖extraction R M Q H g p D c c' μ α eps u far abs side k j per f b‖ ≤ exp (-q*Λ j)

theorem signed {hG:G.Simple} (N:WilsonPrescription G) {S:Prescription B₀} {dial:Bool}
    (issued:Main.Match N hG M S dial) (rows:WilsonPhysicalExteriorFirstCutPrice.Rows R M Q)
    (fund:Windows R M Q) (g:Test 2) (good:∀z,(g z).im=0 ∧ 0≤(g z).re) (pop:Nonempty (tsupport g))
    (nondeg:IsUnit (MSSeparatedTestGram.matrix M H 0 0 g)) : Direct R M Q H g:=by
  intro n p D c c' slow h₁ h₂ h₃ lo μ α q k
  obtain ⟨C,hC,m,returnAt⟩:=WilsonPhysicalExteriorRichFarReturn.measured R M Q H N issued rows g good pop nondeg
    slow h₁ h₂ h₃ lo μ k
  let F:=antidiagonal k
  have acquire(i:Fin (k+1)):=WilsonPhysicalExteriorTestedDetector.measured R M Q fund H p D c c' slow h₁ h₂ h₃ lo μ α
    (q+1) i.val (H+m)
  have rev:=tendsto_exp_atTop.comp (Literal.lambda_leads R.family hG)
  filter_upwards [returnAt,(Filter.eventually_all).mpr acquire,
    rev.eventually_ge_atTop ((F.card:ℝ)*(Fintype.card I:ℝ)*C),
    (WilsonPhysicalExteriorCompactWindow.recedes R hG slow h₁).eventually_ge_atTop 1]
    with j issue bank reserve ht u far abs side per hp eps he f hs hm b
  let t:=T₀ c' j
  let V:=WilsonPhysicalExteriorRichFarReturn.returned R Q H g c c' side (fun _=>μ) (j,per)
  let readRow:=fun l=>reader R M Q p D c c' μ α eps u far abs side l j per f
  have recv:= (issue per hp side).2.2
  have pb:b.size≤H:=by change b.1.val≤H;have :=b.1.isLt;omega
  have pt:0<t:=zero_lt_one.trans_le ht
  have ln:0≤log t:=log_nonneg ht
  have cap:(1+log t)^m≤t^m:=pow_le_pow_left₀ (by linarith only [ln]) (by linarith only [log_le_sub_one_of_pos pt]) _
  have entry (r:ℕ×ℕ) (hr:r∈F) (a:I):‖readRow r.2 a*coeff r.1 (V a b)‖≤C*exp (-(q+1)*Λ j):=by
    have ord:=mem_antidiagonal.mp hr
    have small:=bank ⟨r.2,by omega⟩ u far abs side per hp eps he f hs hm
    have fee:‖coeff r.1 (V a b)‖ ≤ C*t^H*t^m:=(recv r.1 (by omega) a b).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht pb) hC) cap
        (pow_nonneg (by linarith only [ln]) _) (mul_nonneg hC (pow_nonneg pt.le _)))
    rw [norm_mul,mul_comm]
    calc
      _ ≤ (C*t^H*t^m)*‖readRow r.2‖ := mul_le_mul fee (norm_le_pi_norm (readRow r.2) a)
        (norm_nonneg _) (mul_nonneg (mul_nonneg hC (pow_nonneg pt.le _)) (pow_nonneg pt.le _))
      _ = C*(t^(H+m)*‖readRow r.2‖):=by rw [pow_add];ring
      _ ≤ _:=mul_le_mul_of_nonneg_left small hC
  change ‖∑r∈F,∑a:I,readRow r.2 a*coeff r.1 (V a b)‖ ≤ _
  calc
    _ ≤ ∑r∈F,∑_:I,C*exp (-(q+1)*Λ j):=by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum;intro r hr
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _=>entry r hr a)
    _ = ((F.card:ℝ)*(Fintype.card I:ℝ)*C)*exp (-(q+1)*Λ j):=by simp only [sum_const,card_univ,nsmul_eq_mul];ring
    _ ≤ exp (Λ j)*exp (-(q+1)*Λ j):=mul_le_mul_of_nonneg_right reserve (exp_pos _).le
    _ = _:=by rw [←exp_add];congr 1;ring

/-- The actual common original R supplies Q, its independent MS data, and one
positive smooth far test before all first-cut reports, arbitrary marked
profiles, physical periods, query fields and subtraction orders. -/
theorem purchased (hG:G.Simple) (books:Books hG R) (N:WilsonPrescription G) (dial:Bool) :
    ∃(S Q:Prescription B₀),Main.Match N hG M S dial ∧ Q.team=S.team ∧
    WilsonPhysicalExteriorFirstCutPrice.Rows R M Q ∧ Windows R M Q ∧
    ∀(H:ℕ){x:E4},(0:E4)≠x→∀U:Set (Points 2),U∈𝓝 (couple 0 x)→
      ∃g:Test 2,tsupport g⊆U ∧ (∀z,(g z).im=0 ∧ 0≤(g z).re) ∧ 0<(g (couple 0 x)).re ∧
        (∫z,g z)=1 ∧ IsUnit (MSSeparatedTestGram.matrix M H 0 0 g) ∧ Direct R M Q H g:=by
  obtain ⟨S,issued,Z,l,Q,teams,_taylor,_period,rows,win⟩:=books N M dial
  refine ⟨S,Q,issued,teams,rows,win,?_⟩
  intro H x hx U loc
  let V:Warehouse G:=⟨R.family.labels,R.family.params,R.family.localSection,R.makes.sections,fun d=>Next.Foundations.valuation G d⟩
  obtain ⟨g,cover,good,pos,one,tree⟩:=MSSeparatedTestGram.localized V M H 0 hx U loc
  have h: g (couple 0 x)≠0:=by intro z;rw [z] at pos;exact lt_irrefl _ pos
  have live:Nonempty (tsupport g):=⟨couple 0 x,subset_closure h⟩
  exact ⟨g,cover,good,pos,one,tree,signed R M Q H N issued rows win g good live tree⟩

end YM.Integration.WilsonPhysicalExteriorRichFarExtraction
end
