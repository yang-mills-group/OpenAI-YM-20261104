import YM.Integration.WilsonOriginalOccupiedDegree
import YM.Integration.WilsonOriginalOccupiedStencil
import YM.QuadraticLocal.Tariff.Measure

/-! The exact signed arity-dependent withdrawal is taken before every outer Wilson integral. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedSource
open Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Fusion QuadraticLocal.Fusion.Attached
open WilsonOriginalOccupiedTap WilsonOriginalOccupiedStencil
open scoped BigOperators Classical
variable {V:Type} [DecidableEq V] [Fintype V] {R:Census V}
variable {G:Gauge} {m:Side} {P:Rep G m} {o:V→Site m} {X I:Type}

def nodes (n:ℕ)(T:ℂ):Finset ℂ:=insert 1 (insert 0 (univ.image fun j:Fin (n+1)=>T*node j))

theorem original (A:Gallery X I o P R) (w:V→ℝ)(wp:∀v,0<w v) (s:R.Mode){n:ℕ}
    (size:s.val.card ≤ n)(T q:ℂ)(inv:T*q=1) {B:ℝ}
    (fund:∀z∈nodes n T,(gallery z A).K.Paid w P.p.B P.p.supportExponent B) (x:X) (U:Config G m):
    ((gallery 1 A).density x U).part s-((gallery 0 A).density x U).part s=
      ∑j:Fin (n+1),weight q j*((gallery (T*node j) A).density x U).part s:=by
  let E:=Poly.pass (A.E.log x U)
  let pack (z:ℂ)(l:Finset ℕ):=Attached.packet P.activities P.p ((gallery z A).K.hard x) U l
  let bill (z:ℂ)(l:Finset ℕ):= (E * pack z l).part s
  have sums (z:ℂ)(eligible:z∈nodes n T): HasSum (bill z) ((E*((gallery z A).gas x U)).part s):=by
    have gas:=Hard.packet_summing _ (fund z eligible) P.p.exponent_pos.le wp x U
    have coffee:HasSum (fun l=>E*pack z l) (E*(gallery z A).gas x U):=gas.hasSum.map (AddMonoidHom.mulLeft E) (continuous_const.mul continuous_id)
    exact (Poly.get s).hasSum coffee
  have row (l:Finset ℕ):bill 1 l-bill 0 l=∑j:Fin (n+1),weight q j*bill (T*node j) l:=by
    obtain ⟨p,deg,read⟩:=WilsonOriginalOccupiedDegree.product (WilsonOriginalOccupiedDegree.constant E)
      (WilsonOriginalOccupiedDegree.packet A x U l) s
    have r (z:ℂ):p.eval z=bill z l:=read z
    simpa only [r] using (WilsonOriginalOccupiedStencil.original p (deg.trans size) T q inv)
  have h1:=sums 1 (by simp [nodes])
  have h0:=sums 0 (by simp [nodes])
  have hj (j:Fin (n+1)):=sums (T*node j) (mem_insert_of_mem (mem_insert_of_mem (mem_image_of_mem _ (mem_univ j))))
  have finite:HasSum (fun l:Finset ℕ=>∑j:Fin (n+1),weight q j*bill (T*node j) l)
      (∑j:Fin (n+1),weight q j*(E*(gallery (T*node j) A).gas x U).part s):=by
    exact hasSum_sum fun j (_:j∈univ)=>(hj j).mul_left (weight q j)
  have full:=(h1.sub h0).tsum_eq.symm.trans ((tsum_congr row).trans finite.tsum_eq)
  have lev (z:ℂ):((gallery z A).density x U).part s=
      (Real.exp (P.exponent U):ℂ)*(E*(gallery z A).gas x U).part s:=rfl
  simp only [lev]
  rw [←mul_sub,full,mul_sum]
  apply sum_congr rfl
  intro j _
  ring

theorem one (A:Gallery X I o P R)(x:X)(U:Config G m):
    (gallery 1 A).density x U=A.density x U:=by
  have gas:(gallery 1 A).gas x U=A.gas x U:=by
    unfold Gallery.gas
    apply tsum_congr
    intro l
    unfold Attached.packet
    split
    · apply prod_congr rfl
      intro j _
      exact identity A.K x j U
    · rfl
  simp only [Gallery.density,gas]
  rfl

end YM.Integration.WilsonOriginalOccupiedSource
