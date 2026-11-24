import YM.Integration.WilsonOriginalAlternativeTrialRegular

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialAnyLamp
open Finset Lattice RG Wilson Marker Multi QuadraticLocal Ac Source Labels Extra.Histories
open QuadraticLocal.Fusion.Attached Push.Local Planned.GuardedAtom Comparison.RG02.Cumulants
open WilsonPrecontactSeparatedLamps
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V X I:Type}[DecidableEq V][Fintype V]
    {o:V→Site n}{J:Census V}{P:Rep G n}{w:V→ℝ}

theorem original (E:Lamps X I G P.p o J)(hw:∀v,0<w v)(wide:5≤P.p.B)
    (apart:∀v k:V,v≠k→P.p.B^2+1 ≤ separation (o v) (o k))
    (paid:E.Paid w P.p.B (P.p.supportExponent+2) 1)(x:X)(s:Hot J)(many:1<s.val.val.card)(U:Config G n):
    Poly.toll w s.val*‖(E.log x U).part s.val‖ ≤ Real.exp (-(2:ℝ)*((P.p.B/8:ℕ):ℝ)):=by
  let F:=portion E (mixed E)
  let O:=portion E (mixed E)ᶜ
  have hf:F.Paid w P.p.B P.p.supportExponent (Real.exp (-(2:ℝ)*((P.p.B/8:ℕ):ℝ))):=by
    simpa only [mul_one] using (at_sites E (a:=P.p.supportExponent) (δ:=2) wide (by norm_num) hw apart paid)
  have base:=lower E (show P.p.supportExponent≤P.p.supportExponent+2 by linarith) hw paid
  have ho:O.Paid w P.p.B P.p.supportExponent 1:=charged E (mixed E)ᶜ base
  have none:(O.log x U).part s.val=0:=by
    change (∑'i,O.frame i x U).part s.val=0
    rw [Poly.share (ho.sums P.p.exponent_pos.le hw x U)]
    have off:∀ i,(O.frame i x U).part s.val=0:=by
      intro i
      have no:s.val≠E.mode i.val:=by
        intro eq
        exact i.property (show 1<(E.mode i.val).val.card from eq ▸ many)
      rw [Lamps.frame,Poly.part_send]
      exact if_neg no
    simp_rw [off]
    simp
  obtain ⟨v,hv⟩:=s.property
  have lowerFee:=WilsonFirstReceivedGalleryRegular.occupied F hf P.p.exponent_pos.le hw x U s.val v hv
  have same:=split E (mixed E) x U (base.sums P.p.exponent_pos.le hw x U)
  change F.log x U+O.log x U=E.log x U at same
  rw [←same,Poly.part_plus,none,add_zero]
  exact lowerFee

end YM.Integration.WilsonOriginalAlternativeTrialAnyLamp
end
