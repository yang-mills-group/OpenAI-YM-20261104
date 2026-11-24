import YM.LocalLTE.Dilation.Clothes
/-! Price lead.Canonical orbital map under actual frame (includes p.threshold). Explicit projector.
 Defines what goes to ψ and f.Ph gains. `fact` exposes one-step diameter transactions in actual order.Aff costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Dilation
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Next.Foundations
open Planned.GuardedAtom Guard Push Local YM.MergeProof
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side}{ι:Type*}{d:ℕ}{F:Labels.Frame G d}{o:Site n}{B:SectionData F}
    {R:Rep G n}
variable {P:BudgetPoint} {A:Hol G} {σ C Λ δ η w e r v g a a' b b₂ c c' d' t : ℝ}
variable {X Y:ℕ→Support n}
lemma factorLarge (h:Local.Readable A B P n e): 1 ≤ Local.factor A B P.supportExponent e:= one_le_mul_of_one_le_of_one_le (Real.one_le_exp (mul_nonneg (add_nonneg P.exponent_pos.le zero_le_two) (by positivity))) (atomPrice_ge_one A F h.nonneg)
lemma usualPerm {W:Rep G n}(h:hitWidth W.p*Real.sqrt w≤1) (hh:0<w): hitWidth W.p*w/Real.sqrt w≤1 ∧ hitWidth W.p*w≤1:=by
   let b:=Real.sqrt w; have hb:0<b:= Real.sqrt_pos.mpr hh
   have ht:b ≤1:= (le_mul_of_one_le_left hb.le (width_one_le ..)).trans h
   have hp: hitWidth W.p*w≤ b:=by nth_rw 1 [← Real.mul_self_sqrt hh.le,← mul_assoc]; exact mul_le_of_le_one_left hb.le h
   exact ⟨(div_le_one hb).mpr hp, hp.trans ht⟩
variable (X) (M:Local.Raw F n) (S:Berths R.p R.activities Y) (S':Berths R.p R.activities (fun i=>joint B o (Y i))) (A)
local notation "W"=> out X M S
local notation "Ω" => hitWidth R.p * w
local notation "θ"=> (fun i=> Dilation.update R.p (X i) (Y i) (M.bulk i))
local notation "D" => Local.factor A B R.p.supportExponent e
local notation "ψ" => clipSum Y θ+coda B A o Y (out X M S) R
local notation "uG"=> mint S' (out X M S) A
variable (h:Fills o X Y R.p g) (hx:R.Lawful σ C Λ δ w)(hw:0<w) (hq:hitWidth R.p*Real.sqrt w≤1) (hr: Local.Readable A B R.p n e)
    (hf:M.Format o X R)
local notation "ρ"=> Real.sqrt w
local notation "ε"=> Ω/ ρ
local notation "tc"=> turnCost R.p.order R.p.power
local notation "oc"=> Motion.orbitCost F
include h hx hw hq hr hf
lemma fact (hu:Tare M o X A B R e w (Real.sqrt w) a b c) (hv:YM.Planned.GuardedAtom.Deck M o X R (Real.sqrt w) a' b₂) (h:a=Local.factor A B R.p.supportExponent e * a') (he:turnCost R.p.order R.p.power*a+(b+c)≤r) (z:F.Coeff) (hT:((∃ f d', Models A o X R.p M z d' f ∧ 0≤d' ∧ Motion.orbitCost F*(errorPrice A F*d') ≤ t) ∨ Motion.orbitCost F*(F.coeffSize (M.seed-z)+a) ≤ t)) (Y':Berths R.p R.activities (fun i=>joint B o (X i))) : let u:=uG; u.Format o A R∧ u.density o B R=M.eval o X B R ∧ oc * F.coeffSize (u.x-z)≤t ∧ (∃ a b:ℝ,Tab u o R ρ a b∧ tc*a+b≤4*g*r) ∧ Attainment R.p o ψ (4*g*r) ∧ profile R.activities u.forced=profile R.activities M.forced+hook R.activities R.p.threshold ψ:=by
    intro u
    have ht:=usualPerm («W»:=R) hq hw; have hr':0<ρ:=Real.sqrt_pos.mpr hw
    have huP:YM.Planned.GuardedAtom.Deck M o X R ρ a' b:=⟨hv.bulk,hu.packets⟩
    have hΛ:Fills o X Y R.p g:=(by assumption)
    obtain ⟨hf',hp',hy,hD,hL⟩:= banner X M S hΛ hx hw.le ht.2 hr hr' hf huP S' -- edit
    have heS:1≤ tc:= by unfold Push.Local.turnCost; exact one_le_pow₀ (one_le_mul_of_one_le_of_one_le one_le_two (one_le_pow₀ one_le_two))
    obtain ⟨hz,hH,hx'⟩:= Tare.costs_nonneg hu hr'; have hh:0≤a':=(hv.costs_nonneg hr').1
    have hW:=hΛ.factor; have hs :u.x=(mint Y' M A).x:= coordinate X M S hΛ hr hf S' Y'
    have hF : D*(g*a')=g*a:= h.symm ▸ mul_left_comm _ _ _
    have he1:1 ≤ D:= factorLarge hr
    have hV : a' ≤ a:= h.symm ▸ le_mul_of_one_le_left hh he1
    have ih: a ≤ tc*a:=le_mul_of_one_le_left hz heS
    have hx1: a≤r:=ih.trans ((le_add_of_nonneg_right (add_nonneg hH hx')).trans he); have hz':0≤ r:= hz.trans hx1
    refine ⟨hf',hp',?_,⟨_,_,hy,?_⟩,stackFee hD ?_,hL⟩
    · rw [hs]; obtain ⟨f,d',hl,hk,hu'⟩|H:= hT
      · exact le_trans (mul_le_mul_of_nonneg_left (sensor Y' hf hr hu hl hk) (zero_le_one.trans (Motion.orbitCost_one_le F))) hu'
      exact le_trans (mul_le_mul_of_nonneg_left (size_mint Y' hf hr hu z) (zero_le_one.trans (Motion.orbitCost_one_le F))) H
    · rw [hF,mul_left_comm _ g]; have he2: 0≤g:=zero_le_one.trans hW
      have hi:tc*a ≤r:=(le_add_of_nonneg_right (add_nonneg hH hx')).trans he
      have hy1: ε*(g*a')≤g*r:= (mul_le_of_le_one_left (mul_nonneg he2 hh) ht.1).trans (mul_le_mul_of_nonneg_left (hV.trans hx1) he2)
      have hy2: ε*(g*a) ≤ g*r:= (mul_le_of_le_one_left (mul_nonneg he2 hz) ht.1).trans (mul_le_mul_of_nonneg_left hx1 he2)
      have hx2:b≤g*r:=(show b≤r by linarith only [hx',ih,hz,he]).trans (le_mul_of_one_le_left hz' hW)
      linarith only [hy1,hy2,hx2, mul_le_mul_of_nonneg_left hi he2]
    · rw [hF]; apply le_trans (add_le_add (mul_le_mul_of_nonneg_left (hV.trans hx1) (zero_le_one.trans hW)) (mul_le_mul_of_nonneg_left hx1 (zero_le_one.trans hW)))
      nlinarith only [mul_nonneg (zero_le_one.trans hW) hz']
end YM.LocalLTE.Dilation
