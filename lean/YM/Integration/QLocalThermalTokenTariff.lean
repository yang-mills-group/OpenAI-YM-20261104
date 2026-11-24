import YM.Integration.QLocalMarkedTouchingPrice
import YM.Integration.QLocalThermalJoinedLaw
import YM.Integration.WilsonCurvatureEndpoints

/-! Absolute spatial tariff of every actual hot path token at a fixed
nonempty source mode. The old rooted fee already includes the fourfold
width reserve used to pay all touching signed compulsory partners. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalThermalTokenTariff
open Function Finset Lattice Wilson RG Marker Overlay Extra.Histories Planned.GuardedAtom
open LocalComparison Comparison.Density.RenderM LocalComparison.MarkedPackets MergeProof.Accent
open Push.AbsoluteSums QLocalThermalPacketDivision QLocalThermalJoinedSource
open ActualWilsonDirtyPartners
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {V:Type} [DecidableEq V] [Fintype V]
    {D:V→ ComparisonDensity.Address.Orbit} {Γ:Census V} (P:MarkedPackets D G n Γ)
    {p:BudgetPoint} {a:V→Support n} {region:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w:V→ℝ} {g width budget:ℝ} {off cov:ℕ}
    (H:P.Paid p a region w g width budget off cov)
include H

def stem (s:Γ.Mode) (w:V→ℝ) (g:ℝ) (i:ℕ) : ℝ :=
  if P.mode i=s then (P.packet i).elim 0
    (fun T=>(2:ℝ)^P.rankCap*(Poly.toll w s*‖(g:ℂ)^P.power i‖*T.coin)) else 0

omit [Fintype V] in
theorem charged (s:Γ.Mode) (r:ℕ) : 0 ≤ stem P s w g r := by
  by_cases h:P.mode r=s
  · cases e:P.packet r with
    | none=>simp [stem,h,e]
    | some T=>
      have hc:0≤T.coin:=(H.coefficient r T e).1
      exact (by simpa only [stem,h,if_pos,Option.elim_some,e] using
        (mul_nonneg (by positivity : 0≤(2:ℝ)^P.rankCap)
          (mul_nonneg (mul_nonneg (Poly.worth H.positive s).le (norm_nonneg _)) hc)))
  · simp [stem,h]

omit [Fintype V] in
theorem field (q:BudgetPoint) (c:ℂ) (hc:‖c‖≤1) (s:Γ.Mode) (r:ℕ) (x:IndependentTests D) (U:Config G n) :
    Poly.toll w s*‖row P q g c s (testInclusion D x) r U‖ ≤ stem P s w g r := by
  by_cases selected:pick P q U r≠none ∧ s=P.mode r
  · cases e:P.packet r with
    | none=>simp [row,selected,MarkedPackets.term,e,stem]
    | some T=>
      let ht:=WilsonCurvatureEndpoints.cold T (testInclusion D x) ((H.coefficient r T e).2 x)
        2 (by norm_num) U (fun _=>G.chord_le_two _)
      have cap:(2:ℝ)^P.rank r≤2^P.rankCap:=pow_le_pow_right₀ (by norm_num) (P.rank_bounded r T e)
      have hv:‖T.read (testInclusion D x) U‖≤T.coin*2^P.rankCap:=
        ht.trans (mul_le_mul_of_nonneg_left cap (H.coefficient r T e).1)
      rw [row,if_pos selected,MarkedPackets.term,stem,if_pos selected.2.symm,e]
      simp only [Option.elim_some,norm_mul]
      have hreal:=mul_le_mul_of_nonneg_left hv (norm_nonneg ((g:ℂ)^P.power r))
      have hlead:=mul_le_mul_of_nonneg_right hc
        (mul_nonneg (norm_nonneg ((g:ℂ)^P.power r)) (norm_nonneg (T.read (testInclusion D x) U)))
      apply (mul_le_mul_of_nonneg_left (hlead.trans (by simpa only [one_mul] using hreal))
        (Poly.worth H.positive s).le).trans_eq
      ring
  · simpa only [row,if_neg selected,norm_zero,mul_zero] using charged P H s r

omit [Fintype V] in
theorem exposure (i:ℕ) (T:Token G n (fun v=>(D v).Mood) (P.rank i)) (e:P.packet i=some T) :
    Real.exp (4*p.supportExponent*coverNumber p.B T.plot)≤
      Real.exp (4*p.supportExponent*(off:ℝ))*Real.exp (width*T.fall) := by
  have hb:(0:ℝ)<p.B:=by exact_mod_cast p.B_pos
  have room:4*p.supportExponent*(cov:ℝ)≤width*p.B:=by
    have h:=(div_le_iff₀ hb).mp H.width_reserved
    linarith only [h]
  rw [←Real.exp_add]
  apply Real.exp_monotone
  apply (mul_le_mul_iff_of_pos_right hb).mp
  have cover:=mul_le_mul_of_nonneg_left (H.cover i T e) (show 0≤4*p.supportExponent by exact mul_nonneg (by norm_num) p.exponent_pos.le)
  have reach:=mul_le_mul_of_nonneg_right room (Nat.cast_nonneg T.fall)
  nlinarith only [cover,reach]

omit [Fintype V] in
theorem fee (s:Γ.Mode) (hs:s≠Γ.quiet) :
    SumBudget (fun i=>stem P s w g i*Real.exp (4*p.supportExponent*coverNumber p.B (plot P i)))
      ((2:ℝ)^P.rankCap*Real.exp (4*p.supportExponent*(off:ℝ))*budget) := by
  have nz:s.val.Nonempty:=by
    apply nonempty_iff_ne_empty.mpr
    intro h
    exact hs (Subtype.ext h)
  obtain ⟨v,hv⟩:=nz
  apply budget_mono (budget_scale (show 0≤(2:ℝ)^P.rankCap*Real.exp (4*p.supportExponent*(off:ℝ)) by positivity) (H.roots v))
  · exact fun i=>mul_nonneg (charged P H s i) (Real.exp_pos _).le
  · intro i
    by_cases here:P.mode i=s
    · cases e:P.packet i with
      | none=>simp [stem,here,e]
      | some T=>
        simp only [stem,here,if_pos,plot,e,Option.elim_some,if_pos hv]
        have u:0≤(2:ℝ)^P.rankCap*(Poly.toll w s*‖(g:ℂ)^P.power i‖*T.coin):=
          mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (Poly.worth H.positive _).le (norm_nonneg _))
            (H.coefficient i T e).1)
        exact (mul_le_mul_of_nonneg_left (exposure P H i T e) u).trans_eq (by ring)
    · simp only [stem,if_neg here,zero_mul]
      exact mul_nonneg (by positivity) ((H.roots v).1 i)

omit [Fintype V] in
theorem partners {A ι:Type*} [DecidableEq ι] (S:ι→Support n) (F:ι→A→Poly Γ) {u:ℝ}
    (old:Towed w S F p.B p.supportExponent u) (small:u*blockSites p.B≤(3*p.supportExponent)/2)
    (s:Γ.Mode) (hs:s≠Γ.quiet) :
    ∃b:ι→ℝ,(∀i,0≤b i ∧ ∀z,Poly.price w (F i z)≤b i) ∧
      SumBudget (fun t:ℕ×Finset ι=>stem P s w g t.1*dirty p S (plot P t.1) b t.2)
        ((2/(3*p.supportExponent))*(u*blockSites p.B)*((2:ℝ)^P.rankCap*Real.exp (4*p.supportExponent*(off:ℝ))*budget)) := by
  apply QLocalMarkedTouchingPrice.source_at p S F H.positive old (mul_pos (by norm_num) p.exponent_pos) small (plot P) _ (charged P H s)
  simpa only [show p.supportExponent+3*p.supportExponent=4*p.supportExponent by ring] using fee P H s hs

end YM.Integration.QLocalThermalTokenTariff
