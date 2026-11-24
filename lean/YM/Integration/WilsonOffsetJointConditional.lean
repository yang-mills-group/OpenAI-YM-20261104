import YM.Integration.WilsonOffsetJointRoster
import YM.Integration.WilsonOffsetMarkComparison

/-! Conditional error for the actual entire planted exterior times a
two-placement signed lamp. Both funded columns use the same old vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOffsetJointConditional
open Function MeasureTheory Lattice RG Wilson Source Labels MSbar.Bulk RGComparison.Core16.Spool
open WilsonConditionalTaylorLabels WilsonOffsetJointRoster WilsonOffsetConditionalCharge WilsonOffsetMarkComparison
open scoped Classical BigOperators
variable {G:Gauge} {c f:Side} {S:StepData c f} {P:Rep G f}
variable (hk:S.IsKernel P.beta G) (hp:Envelope P.eval) (V:Config G c)

include hk hp in
theorem tested (a:Roster G) (s:Finset (Fin a.length)) (i:Fin a.length) (hi:i∈s)
    (o:Fin a.length→Site f) (z e:Site f) (w k:Bool→ℝ) (δ:ℝ)
    (qw:∀b,|expect S P V (fun U=>look b (field a s (Function.update o i z) U))-w b|≤δ)
    (qk:∀b,|expect S P V (fun U=>look b (field a s (Function.update o i e) U))-k b|≤δ):
    ‖conditional S P V (fun U=>field a (s.erase i) o U*(WilsonOffsetJointRoster.one a i z U-WilsonOffsetJointRoster.one a i e U))-(paint w-paint k)‖≤4*δ:=by
  let A:=field a s (Function.update o i z)
  let B:=field a s (Function.update o i e)
  have ha:Continuous A:=tally_cont _ _
  have hb:Continuous B:=tally_cont _ _
  have same:(fun U=>field a (s.erase i) o U*(WilsonOffsetJointRoster.one a i z U-WilsonOffsetJointRoster.one a i e U))=(fun U=>A U-B U):=by
    funext U;exact (paired a s i hi o z e U).symm
  rw [same,subtract hk hp V A B ha hb]
  calc ‖(conditional S P V A-conditional S P V B)-(paint w-paint k)‖
      =‖(conditional S P V A-paint w)-(conditional S P V B-paint k)‖:=by congr 1;ring
       _≤_:= (norm_sub_le _ _).trans (show ‖conditional S P V A-paint w‖+‖conditional S P V B-paint k‖≤4*δ from by
               linarith only [WilsonOffsetMarkComparison.one hk hp V A ha w δ qw,WilsonOffsetMarkComparison.one hk hp V B hb k δ qk])

end YM.Integration.WilsonOffsetJointConditional
