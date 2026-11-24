import YM.Integration.WilsonOriginalPrimerLampJet
import YM.Integration.WilsonElectedPrimaryTensor
import YM.QuadraticLocal.Poetry.Agenda

/-! The located, unsigned-test field used by the physical source is
summed with every funded signed curvature coefficient and its own coupling
power. This comparison applies on a moving link curve. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPrimerRollJet
open Function Filter Finset Lattice Laurent RG Wilson Stationary
open Primitives.TwoWave QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary PositionX.Jet PositionX.Gauss
open AllOrder AllOrder.Fire AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{n:Side}

theorem located (x:Site n) : Picket.pinpoint () x (fun _=>1) = WilsonElectedPrimaryTensor.pin x:=by
  funext z
  by_cases h:z.1=x <;> simp [Picket.pinpoint,WilsonElectedPrimaryTensor.pin,h]

theorem original (W:Roll G Unit)(l d j:ℕ)(d0:0<d){a C:ℝ}(ha:0<a)
    (paid:W.Faith {()} () (l+d+2) a C) (x:Site n)
    (f:ℝ→Link G n)(hf:ContDiffAt ℝ ω f 0):
    HasSum (fun u:W.Ty=>someJ (fun t:ℝ=>t^(l+d+1-(W.leg u).r)*
      (W.leg u).atom.unmasked (Haiku.life f t) x) (j+d+1))
    (weigh f (fun e A=>(W.folded l e).table n (mingle A (WilsonElectedPrimaryTensor.pin x))) j):=by
  let H:Finset Unit:={()}
  let I:Unit→Loan:=fun _=>⟨0,0,d,d0,by omega⟩
  let N:=max l j
  let b:=Agenda.descent a I H N
  have guard:Agenda.guard I H l=l+d+2:=by simp [Agenda.guard,plusK,I,H]
  have H₀ (e:ℕ)(h:e≤j): ∃ K, Roll.Posture Unit G H () K a b (l+d+2) l e:=by
    rw [←guard]
    exact Agenda.scope H () I e (h.trans (le_max_right ..)) ha le_rfl (Agenda.day H I N ha).1 (le_max_left ..)
  choose K δ using H₀
  let ones:rule Unit n:=fun _=>1
  have invoice (u:W.Ty) : Ink.invoice x (W.leg u).roots ones=1:=by
    simp [Ink.invoice,Ink.paid,ones,Function.comp_def]
  have cost (u:W.Ty):(W.leg u).r≤l+d+1:=by
    have upper:(W.leg u).r+(W.leg u).roots.length≤l+d+2:=(paid.pinned u).tall
    have owned:0<(W.leg u).roots.length:=List.length_pos_of_mem (paid.pinned u).owns
    omega
  have site (e:ℕ)(he:e≤j):
      (fun A=>(W.folded l e).site n x (mingle A ones))=
      fun A=>(W.folded l e).table n (mingle A (WilsonElectedPrimaryTensor.pin x)):=by
    funext A
    rw [←located]
    exact (Picket.Fixed.receipt H () _ (W.stays H () l (δ e he) paid) A ones x).symm
  have allwords : HasSum (fun u:W.Ty=>weigh f (Lantern.gleam (W.leg u) x ones l) j)
    (weigh f (fun e A=>(W.folded l e).site n x (mingle A ones)) j):=
    hasSum_sum (s:=range (j+1)) (fun e he=> W.weighed H () l (δ e (by have:=mem_range.mp he; omega))
      paid x ones f hf (j-e))
  have eq:weigh f (fun e A=>(W.folded l e).site n x (mingle A ones)) j=
      weigh f (fun e A=>(W.folded l e).table n (mingle A (WilsonElectedPrimaryTensor.pin x))) j:=by
    unfold weigh
    apply Finset.sum_congr rfl
    intro e he
    exact congrArg (fun g:Link G n→ℝ=>someJ (g ∘ f) (j-e)) (site e (by have:=mem_range.mp he; omega))
  rw [←eq]
  refine allwords.congr_fun (fun u=>?_)
  simpa only [Lantern.light,invoice,mul_one] using
    WilsonOriginalPrimerLampJet.earned (W.leg u) x ones l d j (cost u) f hf

end YM.Integration.WilsonOriginalPrimerRollJet
end
