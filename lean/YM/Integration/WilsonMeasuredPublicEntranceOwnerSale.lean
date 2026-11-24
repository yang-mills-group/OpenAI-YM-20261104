import YM.Integration.WilsonMeasuredPublicEntranceOwnerGas
import YM.Integration.WilsonMeasuredPublicEntrancePeerFace
import YM.Integration.WilsonSeparatedPrefixCanonicalCarton
import YM.Integration.WilsonSeparatedPrefixCanonicalFares

/-! Put a single genuine forced owner next to a finite arbitrary family of
regular peers, before doubling the marks for the Wilson flat measurements. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceOwnerSale
open Function Finset Lattice Wilson RG Source Labels Marker Extra.Histories Push.Local
open MergeProof MergeProof.Accent Push.GridApprox.Nil
open Extra.Trajectories
open WilsonMeasuredCoefficientTransport WilsonMeasuredPublicEntranceOwnerGas
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{d:ℕ}{F:Labels.Frame G d}{V:Type}[Fintype V][DecidableEq V]{J:Census V}
variable (P:Rep G n)(φ:V → Config G n→ℂ)(q:Coefficient F n)(v:V)
local notation "full" => (restore (B:=J) P φ (selected P q v) 0 0)

/-- Any authentic sale at this date grants the zero mixed rates at its own
original wage. The separately charged named hard and regular fields are kept. -/
theorem stocked {o:V→Site n}{w:V→ℝ}{e:ℝ}{x:V → Config G n→ℂ}{h:V → Box n → Config G n→ℂ}{F₀:Config G n → Poly J}
    (wp:∀i,0<w i)(source:Served P x h F₀ o w e 1):Served P φ (selected P q v) full o w e 1:=by
  obtain ⟨H,K,cart,hi,ki,_⟩:=source
  have geometry: Carton o (0:Support n → Config G n → Poly J) (0:Box n → Config G n → Poly J) P.p.threshold:=by
    simpa only [Pi.zero_def,zero_smul] using WilsonSeparatedPrefixCanonicalCarton.rescale cart (0:ℂ)
  have hs:Towed w id (0:Support n → Config G n → Poly J) P.p.B e 0:=by
    simpa only [Pi.zero_def,zero_smul,norm_zero,zero_mul] using WilsonSeparatedPrefixCanonicalFares.scale hi (0:ℂ)
  have ks:Towed w Prod.fst (0:Box n → Config G n → Poly J) P.p.B e 0:=by
    simpa only [Pi.zero_def,zero_smul,norm_zero,zero_mul] using WilsonSeparatedPrefixCanonicalFares.scale ki (0:ℂ)
  exact ⟨0,0,geometry,hs.shrink le_rfl zero_le_one wp,ks.shrink le_rfl zero_le_one wp,rfl⟩

theorem fieldwise {a b κ B:ℝ}(valid:P.activities.Valid P.p a b){o:Site n}(fee:q.remBound o P κ B)
    (s:J.Mode)(inside:v∈s.val)(U:Config G n):
    (full U).part s-(P.eval U:ℂ)*(∏i∈s.val,φ i U)=
      account q P U*(∏i∈s.val.erase v,φ i U):=by
  classical
  let E:=Poly.pass (Mach J (fun i=>φ i U))
  let time:ℂ:=Real.exp (P.exponent U)
  let count:ℂ:=∑' k,q.marked P k U
  let gas₀:=Poly.bead J (P.activities.gas P.p U)
  have packed:=WilsonMeasuredPublicEntranceOwnerGas.original (J:=J) P q v valid fee U
  have raw:(full U)=time • (E*(gas₀+Poly.send (J.fire v) count)):=by
    unfold restore
    simp only [Pi.zero_apply,add_zero,sum_const_zero]
    rw [packed]
  have quiet:(time • (E*gas₀)).part s=(P.eval U:ℂ)*(∏i∈s.val,φ i U):=by
    rw [mul_comm E,Poly.product_bead,smul_smul,Poly.part_smul]
    simp only [E,Mach,pass_fire,Rep.eval,Complex.ofReal_mul,time]
  have pin:Poly.send (J.fire v) count=count • Poly.send (J.fire v) 1:=by
    ext1 i
    simp only [Poly.part_smul,Poly.part_send]
    split <;> simp
  rw [raw,mul_add,smul_add,Poly.part_plus,quiet,add_sub_cancel_left,pin,mul_smul_comm,smul_smul,Poly.part_smul,
    WilsonMeasuredPublicEntrancePeerFace.select E v s inside]
  simp only [E,Mach,pass_fire,time,count,account]

end YM.Integration.WilsonMeasuredPublicEntranceOwnerSale
end
