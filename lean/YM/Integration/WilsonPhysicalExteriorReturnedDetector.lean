import YM.Integration.WilsonPhysicalExteriorTestedDetector

/-! The full coefficient of the sharp two-sided Gram inverse applied to
the actually measured far-probe errors. The probe, both field rosters and
every signed lower coupling order are retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorReturnedDetector
open Filter Set Function Real Matrix Finset MeasureTheory PowerSeries Lattice RG RG16
open PhysicalNext.Repeat.Legato Pert Pert.Position MS MS.Land MS.Menus MS.Rake MS.Tone
open FVA2 FVA2.ColorCode Register FVAAlt2 Lobby Extra.FD
open WilsonPhysicalExteriorIssuedWord WilsonPhysicalExteriorTestedDetector
open WilsonPhysicalExteriorSmoothGram
open scoped Topology BigOperators Classical
variable {G:Gauge}
local notation "B₀" => Press.portDeck G
local notation "M₀" => MS_Data G (Position.OpenAxis.Plot B₀)

def returned (R:Run G) (M:M₀) (Q:Prescription B₀) (h:ℕ) (g:Test 2)
    (hg:IsUnit (MSSeparatedTestGram.matrix M h 0 0 g)) {n:ℕ} (p:Fin n→Label B₀) (D:Design n)
    (c c' μ:ℝ) (α eps:Fin (n+1)→ℝ) (u e:Fin (n+1)→Bool) (a side:Bool) (k j per:ℕ)
    (f:Glyph B₀ h→Test (n+1)) : Glyph B₀ h→ℂ :=
  ∑r∈antidiagonal k,(coeff r.1 (decoder M h g hg μ (log (WilsonPhysicalExteriorFirstCutScale.ratio R c' j)))).vecMul
    (reader R M Q p D c c' μ α eps u e a side r.2 j per f)

def Sharp (R:Run G) (M:M₀) (Q:Prescription B₀) (h:ℕ) (g:Test 2)
    (hg:IsUnit (MSSeparatedTestGram.matrix M h 0 0 g)) : Prop :=
  ∀(μ:ℝ)(N:ℕ),∃C:ℝ,0≤C ∧ ∃m:ℕ,∀(n:ℕ)(p:Fin n→Label B₀)(D:Design n)
    (c c':ℝ)(α eps:Fin (n+1)→ℝ)(u e:Fin (n+1)→Bool)(a side:Bool)(k j per:ℕ),
    k≤N→1≤WilsonPhysicalExteriorFirstCutScale.ratio R c' j→∀f:Glyph B₀ h→Test (n+1),
      let T:=WilsonPhysicalExteriorFirstCutScale.ratio R c' j
      ‖returned R M Q h g hg p D c c' μ α eps u e a side k j per f‖≤
        C*T^h*(1+log T)^m*
          ∑r∈antidiagonal k,‖reader R M Q p D c c' μ α eps u e a side r.2 j per f‖

def Fast (R:Run G) (M:M₀) (Q:Prescription B₀) (h:ℕ) (g:Test 2)
    (hg:IsUnit (MSSeparatedTestGram.matrix M h 0 0 g)) : Prop :=
  ∀(n:ℕ)(p:Fin n→Label B₀)(D:Design n)(c c':ℝ)
    (_:∀m,((R.family.S.block m).val:ℝ)≤log (RG16.Lambda R.family.path.levels m))
    (_:1<c') (_:c'<c) (_:c<2) (lo:ℕ→ℕ) (μ:ℝ) (α:Fin (n+1)→ℝ) (q:ℝ)(k:ℕ),
    ∀ᶠ j:ℕ in atTop,∀u e:Fin (n+1)→Bool,∀a side:Bool,
      ∀per≥WilsonPhysicalExteriorActualSides.floor R c lo j,∀eps:Fin (n+1)→ℝ,
      (∀i,exp (-WilsonPhysicalExteriorActualSides.time R c j)/WilsonPhysicalExteriorFirstCutScale.ratio R c' j≤eps i) →
      ∀f:Glyph B₀ h→Test (n+1),(∀i,tsupport (f i)⊆D.K)→(∀i,(∫z,‖f i z‖)≤1)→
      ‖returned R M Q h g hg p D c c' μ α eps u e a side k j per f‖≤exp (-q*RG16.Lambda R.family.path.levels j)

private theorem computed (R:Run G) (M:M₀) (Q:Prescription B₀) (hG:G.Simple) (fund:Windows R M Q)
    (h:ℕ) (g:Test 2) (hg:IsUnit (MSSeparatedTestGram.matrix M h 0 0 g))
    (sharp:Sharp R M Q h g hg) : Fast R M Q h g hg := by
  intro n p D c c' slow h₁ h₂ h₃ lo μ α q k
  obtain ⟨C,hC,m,price⟩:=sharp μ k
  let T:=WilsonPhysicalExteriorFirstCutScale.ratio R c'
  let Λ:=RG16.Lambda R.family.path.levels
  let S:=antidiagonal k
  have acquire(l:Fin (k+1)):=WilsonPhysicalExteriorTestedDetector.measured R M Q fund h p D c c' slow
    h₁ h₂ h₃ lo μ α (q+1) l.val (h+m)
  have rate:=tendsto_exp_atTop.comp (Literal.lambda_leads R.family hG)
  filter_upwards [Filter.eventually_all.mpr acquire,rate.eventually_ge_atTop ((S.card:ℝ)*C),
    (WilsonPhysicalExteriorCompactWindow.recedes R hG slow h₁).eventually_ge_atTop 1]
    with j hj hconst ht u e a side per hp eps he f hs hm
  have tnon:0≤T j:=zero_le_one.trans ht
  have logbound:1+log (T j)≤T j:=by linarith only [log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one ht)]
  have powers: (1+log (T j))^m≤(T j)^m:=pow_le_pow_left₀ (by linarith only [log_nonneg ht]) logbound m
  let v:=fun l=>reader R M Q p D c c' μ α eps u e a side l j per f
  have pr:=price n p D c c' α eps u e a side k j per le_rfl ht f
  calc
    _≤∑r∈S,C*(T j)^h*(1+log (T j))^m*‖v r.2‖:=by rw [←mul_sum];exact pr
    _≤∑r∈S,C*exp (-(q+1)*Λ j):=by
      apply sum_le_sum;intro r hr
      have le:r.2≤k:=by have hh:=mem_antidiagonal.mp hr;omega
      have small:=hj ⟨r.2,by omega⟩ u e a side per hp eps he f hs hm
      calc
        _≤C*(T j)^h*(T j)^m*‖v r.2‖:=mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left powers (mul_nonneg hC (pow_nonneg tnon h))) (norm_nonneg _)
        _=C*((T j)^(h+m)*‖v r.2‖):=by rw [pow_add];ring
        _≤_:=mul_le_mul_of_nonneg_left small hC
    _≤exp (Λ j)*exp (-(q+1)*Λ j):=by
      simp only [sum_const,nsmul_eq_mul,←mul_assoc]
      exact mul_le_mul_of_nonneg_right hconst (exp_pos _).le
    _=_:=by rw [←exp_add];congr 1;ring

/-- The same source that supplies the finite charged word fixes its true
localized smooth MS Gram *before* every later subtraction scale, order,
independent field menu, genuine mesh/period, and signed compact test. -/
theorem measured (R:Run G) (M:M₀) (Q:Prescription B₀) (hG:G.Simple) (fund:Windows R M Q)
    (h:ℕ) {p:E4} (hp:(0:E4)≠p) (U:Set (Points 2)) (hu:U∈𝓝 (couple 0 p)) :
    ∃g:Test 2,tsupport g⊆U ∧ (∀z,(g z).im=0 ∧ 0≤(g z).re) ∧
      0<(g (couple 0 p)).re ∧ (∫z,g z)=1 ∧ ∃hg:IsUnit (MSSeparatedTestGram.matrix M h 0 0 g),
      (∀μ s,WilsonPhysicalExteriorSmoothGram.far M h g μ s*decoder M h g hg μ s=1 ∧
        decoder M h g hg μ s*WilsonPhysicalExteriorSmoothGram.far M h g μ s=1) ∧
      Sharp R M Q h g hg ∧ Fast R M Q h g hg := by
  let V:Warehouse G:=⟨R.family.labels,R.family.params,R.family.localSection,R.makes.sections,fun d=>Next.Foundations.valuation G d⟩
  obtain ⟨g,loc,pos,ok,unit,hg,both,cost⟩:=WilsonPhysicalExteriorSmoothPrice.purchased M h V hp U hu
  have own:Sharp R M Q h g hg:=by
    intro μ N;obtain ⟨C,hC,m,bank⟩:=cost μ N
    refine ⟨C,hC,m,?_⟩
    intro n fields D c c' α eps u e a side k j per hk ht f
    dsimp only
    rw [returned,mul_sum]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum;intro r hr
    have h:=mem_antidiagonal.mp hr
    exact bank _ ht r.1 (by omega) _
  exact ⟨g,loc,pos,ok,unit,hg,both,own,computed R M Q hG fund h g hg own⟩

end YM.Integration.WilsonPhysicalExteriorReturnedDetector
end
