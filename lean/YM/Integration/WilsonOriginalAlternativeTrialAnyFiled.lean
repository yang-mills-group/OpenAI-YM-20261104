import YM.Integration.WilsonOriginalAlternativeTrialAnyLamp
import YM.Integration.WilsonOriginalAlternativeTrialPartitions

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialAnyFiled
open Finset Lattice RG Wilson Marker Multi QuadraticLocal Ac Source Labels Extra.Histories
open QuadraticLocal.Fusion.Attached Push.Local Planned.GuardedAtom Comparison.RG02.Cumulants
open WilsonPrecontactSeparatedLamps
open private YM.Integration.WilsonOriginalAlternativeTrialPartitions.entry from YM.Integration.WilsonOriginalAlternativeTrialPartitions
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V X I:Type}[DecidableEq V][Fintype V]
    {o:V→Site n}{J:Census V}{P:Rep G n}{w:V→ℝ}
omit [Fintype V] in
private theorem off (E:Lamps X I G P.p o J)(x:X)(U:Config G n)(s:J.Mode)
    (paid:Summable (fun i=>E.frame i x U))(different:∀i,s≠E.mode i):(E.log x U).part s=0:=by
  change (∑'i,E.frame i x U).part s=0
  rw [Poly.share paid]
  have zero:∀i,(E.frame i x U).part s=0:=by
    intro i
    rw [Lamps.frame,Poly.part_send]
    exact if_neg (different i)
  simp_rw [zero]
  simp

theorem original (E:Lamps X I G P.p o J)(hw:∀v,0<w v)
    (paid:E.Paid w P.p.B P.p.supportExponent 1)(x:X)(U:Config G n)(s:J.Mode):
    (Poly.pass ((portion E (mixed E)ᶜ).log x U)).part s=∏j∈s.val,(E.log x U).part (J.fire j):=by
  let F:=portion E (mixed E)
  let O:=portion E (mixed E)ᶜ
  have hF:=charged E (mixed E) paid
  have hO:=charged E (mixed E)ᶜ paid
  have same:=split E (mixed E) x U (paid.sums P.p.exponent_pos.le hw x U)
  change F.log x U+O.log x U=E.log x U at same
  have structure_:O.log x U=WilsonOriginalAlternativeTrialPartitions.unary (E.log x U):=by
    ext t
    rw [YM.Integration.WilsonOriginalAlternativeTrialPartitions.entry]
    by_cases one:t.val.card=1
    · have none:(F.log x U).part t=0:=by
        apply off F x U t (hF.sums P.p.exponent_pos.le hw x U)
        intro i h
        have large:1<(E.mode i.val).val.card:=i.property
        change t=E.mode i.val at h
        rw [←h,one] at large
        exact (lt_irrefl _ large)
      rw [if_pos one,←same,Poly.part_plus,none,zero_add]
    · rw [if_neg one]
      apply off O x U t (hO.sums P.p.exponent_pos.le hw x U)
      intro i h
      have small:¬1<(E.mode i.val).val.card:=i.property
      have p:0<(E.mode i.val).val.card:=card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr (fun h=>E.live i.val (Subtype.ext h)))
      change t=E.mode i.val at h
      rw [h] at one
      omega
  change (Poly.pass (O.log x U)).part s=_
  rw [structure_]
  exact Extra.Trajectories.pass_fire _ _

theorem rated (E:Lamps X I G P.p o J)(hw:∀v,0<w v)(wide:5≤P.p.B)
    (apart:∀v k:V,v≠k→P.p.B^2+1 ≤ separation (o v) (o k))
    (paid:E.Paid w P.p.B (P.p.supportExponent+2) 1)(x:X)(U:Config G n)(s:J.Mode):
    Poly.toll w s*‖(Poly.pass (E.log x U)).part s-∏j∈s.val,(E.log x U).part (J.fire j)‖ ≤
    (shards J s).card*Real.exp (-(2:ℝ)*((P.p.B/8:ℕ):ℝ)):=by
  have base:=lower E (show P.p.supportExponent≤P.p.supportExponent+2 by linarith) hw paid
  apply WilsonOriginalAlternativeTrialPartitions.original w hw _ (E.quiet_of_hasSum x U (base.sums P.p.exponent_pos.le hw x U)) _ (Real.exp_nonneg _)
  · intro t
    obtain ⟨j,hj⟩:=t.property
    exact WilsonFirstReceivedGalleryRegular.occupied E base P.p.exponent_pos.le hw x U t.val j hj
  · intro t big
    exact WilsonOriginalAlternativeTrialAnyLamp.original E hw wide apart paid x t big U

end YM.Integration.WilsonOriginalAlternativeTrialAnyFiled
end
