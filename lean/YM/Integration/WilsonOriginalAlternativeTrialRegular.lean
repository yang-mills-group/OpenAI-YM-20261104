import YM.Integration.WilsonOriginalOccupiedClear
import YM.Integration.WilsonThermometerSolitarySeparationSalary
import YM.Integration.WilsonThermometerSolitaryRegularHead

/-! The genuinely emitted mixed regular part of the three-socket restart,
tested on all held fields and retaining its actual ordinary singleton rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialRegular
open Finset Lattice RG Wilson Marker Multi QuadraticLocal Ac Source Labels Extra.Histories
open QuadraticLocal.Fusion.Attached Push.Local Planned.GuardedAtom Comparison.RG02.Cumulants
open WilsonThermometerSolitaryRegularHead WilsonThermometerSolitaryFiledExchange
open WilsonThermometerSolitaryExchange
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {V X I:Type} [DecidableEq V] [Fintype V]
    {o:V→Site n} {J:Census V} {P:Rep G n} {w:V→ℝ}

theorem printed (E:Lamps X I G P.p o J) (hw:∀v,0<w v)
    (regular:E.Paid w P.p.B P.p.supportExponent 1) (x:X)(s:J.Mode)(U:Config G n):
    Poly.toll w s*‖(Poly.pass (E.log x U)).part s‖ ≤ (shards J s).card:=by
  have each(t:Hot J): Poly.toll w t.val * ‖(E.log x U).part t.val‖ ≤ 1:=by
    obtain ⟨v,hv⟩:=t.property
    exact WilsonFirstReceivedGalleryRegular.occupied E regular P.p.exponent_pos.le hw x U t.val v hv
  have shard (q:(parts J).Mode)(ok:q∈shards J s):
      Poly.toll w s*‖∏t∈q.val,(E.log x U).part t.val‖ ≤ 1:=by
    have split : Poly.toll w s=∏t∈q.val,Poly.toll w t.val:=by
      rw [←show unionOf q=s from (mem_filter.mp ok).2]
      exact prod_biUnion (parts_wise q)
    rw [split,norm_prod,←prod_mul_distrib]
    exact prod_le_one (fun t _=>mul_nonneg (Poly.worth hw _).le (norm_nonneg _)) (fun t _=>each t)
  rw [pass_partition _ (E.quiet_of_hasSum x U (regular.sums P.p.exponent_pos.le hw x U))]
  calc
    _ ≤ Poly.toll w s * ∑p∈shards J s,‖∏t∈p.val,(E.log x U).part t.val‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le ..) (Poly.worth hw _).le
    _ = ∑p∈shards J s,Poly.toll w s * ‖∏t∈p.val,(E.log x U).part t.val‖:=mul_sum .. 
    _ ≤ ∑_∈shards J s,(1:ℝ):=sum_le_sum (fun q hq=>shard q hq)
    _ = _:=by simp

local notation "modes" => Stock.census (Fin 3)

theorem original {p:Fin 3→Site n} (A:Gallery X I p P (modes)) (r:Fin 3→ℝ)
    (positive:∀v,0<r v) (wide:5≤P.p.B)
    (apart:∀v k:Fin 3,v≠k→P.p.B^2+1≤ separation (p v) (p k))
    (regular:A.E.Paid r P.p.B (P.p.supportExponent+2) 1)
    {κ:ℝ} (hard:A.K.Paid r P.p.B P.p.supportExponent κ)
    (x:X)(s:(modes).Mode)(U:Config G n)(vac:P.eval U≠0):
    Poly.toll r s*‖(Poly.pass (A.E.log x U)).part s-(word (value A.E x U)).part s‖ ≤
      2*((shards (modes) s).card:ℝ)*(Real.exp (2*(P.p.B/8:ℕ)))⁻¹:=by
  let T:=Real.exp (2*(P.p.B/8:ℕ))
  have tp:0<T:=Real.exp_pos _
  have tc:(T:ℂ)≠0:=Complex.ofReal_ne_zero.mpr tp.ne'
  have v0:(P.eval U:ℂ)≠0:=Complex.ofReal_ne_zero.mpr vac
  have priced (c:ℂ)(hc:‖c‖≤T):(dyed c A.E).Paid r P.p.B P.p.supportExponent 1:=
    WilsonThermometerSolitarySeparationSalary.separated A.E positive wide apart regular c hc
  have base:=WilsonPrecontactSeparatedLamps.lower A.E (show P.p.supportExponent≤P.p.supportExponent+2 by linarith) positive regular
  have p0:=priced 0 (by simpa using tp.le)
  have pT:=priced T (by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos tp])
  have nodal:=WilsonThermometerSolitaryRegularHead.original A (inv_mul_cancel₀ tc) r positive base p0 pT hard x U s
  have erased:= (WilsonThermometerSolitaryVacuumOpponent.original (dyed 0 A.E) A r positive hard).2 x U
  have raised:= (WilsonThermometerSolitaryVacuumOpponent.original (dyed T A.E) A r positive hard).2 x U
  change (P.eval U:ℂ)*_ = ((T:ℂ)⁻¹)*(_-_) at nodal
  rw [show (endpoint (T:ℂ) A).density x U=_ from raised, show (endpoint 0 A).density x U=_ from erased] at nodal
  let Z (c:ℂ):=(Poly.pass ((dyed c A.E).log x U)).part s
  change (P.eval U:ℂ)*_=(T:ℂ)⁻¹*((P.eval U:ℂ)*Z T-(P.eval U:ℂ)*Z 0) at nodal
  have eqn:(Poly.pass (A.E.log x U)).part s-(word (value A.E x U)).part s=(T:ℂ)⁻¹*(Z T-Z 0):=by
    apply mul_left_cancel₀ v0
    calc _ = _ := nodal
         _ = _ := by ring
  have left:=printed (dyed (T:ℂ) A.E) positive pT x s U
  have right:=printed (dyed 0 A.E) positive p0 x s U
  have both:Poly.toll r s*‖Z T-Z 0‖ ≤ (shards (modes) s).card+(shards (modes) s).card:=by
    calc _ ≤ Poly.toll r s*(‖Z T‖+‖Z 0‖):=mul_le_mul_of_nonneg_left (norm_sub_le ..) (Poly.worth positive _).le
         _ = _ := mul_add ..
         _ ≤ _ := add_le_add left right
  rw [eqn,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos tp]
  calc _ = (Poly.toll r s*‖Z T-Z 0‖)*T⁻¹:=by ring
       _ ≤ _ := by
         change _ ≤ 2*((shards (modes) s).card:ℝ)*T⁻¹
         rw [two_mul ((shards (modes) s).card:ℝ)]
         exact mul_le_mul_of_nonneg_right both (inv_nonneg.mpr tp.le)

end YM.Integration.WilsonOriginalAlternativeTrialRegular
end
