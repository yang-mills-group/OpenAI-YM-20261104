import YM.Integration.WilsonMeasuredPublicEntranceTrialPeerBoard
/-! The reached ordinary lamps can be combined with the cropped part of the
canonical peers under the same optical mask. The two full original densities
are integrated in the Wilson posterior at each earlier boundary value. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHeldCrop
open Function Finset MeasureTheory Lattice Wilson RG Labels Source Marker QuadraticLocal
open Push.Local Push.AbsoluteSums PhysicalNext PhysicalNext.Repeat Legato Extra.Histories
open WilsonMeasuredPublicEntranceOrder WilsonThermometerUnitFilingFieldRange WilsonMeasuredCoefficientTransport
open WilsonOriginalAlternativeHearing WilsonThermometerUnitFilingCoarse
open WilsonMeasuredPublicEntranceCroppedPeer WilsonMeasuredPublicEntranceLampFamily
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){V T I:Type}[DecidableEq V][Fintype V][Countable I](J:Census V)
  {N f p:ℕ}(cut:f≤N)(d:V→ℕ)(ref:∀v,R.family.ref (d v)≤f)(o:V→Site (R.family.side f p))
  (W:Rep G (R.family.side f p))(target:W.p=(R.family.path.rep N p f).p)
  (same:W.eval=(R.family.path.rep N p f).eval)
  (q:(v:V) → Coefficient (R.family.labels.level (d v)) (R.family.side f p))
  (E:Lamps T I G W.p o J)(x:T)(trial:Finset V)(w:V→ℝ)(wp:∀v,0<w v)(D:V→ℕ)
local notation "P" => R.family.path.rep N p f
local notation "cfg" => Config G (R.family.side f p)
open WilsonMeasuredPublicEntranceTrialPeerBoard (field clipped price)
open private linear from YM.Integration.WilsonOriginalAlternativeHearing
local notation "Φ" => field (N:=N) R J d o W q E x trial
local notation "φ" => clipped (N:=N) R J d o W q E x trial D
include cut ref target same wp in
theorem original {κ B:V→ℝ}{A:ℝ}(fit:∀v,(q v).Format (o v) R.family.params P)
    (fees:∀v,(q v).remBound (o v) P (κ v) (B v))(room:1≤(P).p.supportExponent)
    (base:E.Paid w W.p.B (W.p.supportExponent+2) A):
    ∃ (K:Type) (_:Countable K) (L:Lamps Unit K G W.p o J),
      L.Paid w W.p.B (W.p.supportExponent+2) (price (N:=N) R d o W q trial w D B A) ∧
      (∀ v(s:J.Mode),v∈s.val→∀U,WilsonMeasuredCompanionFace.peers L v s () U=∏i∈s.val.erase v,φ i U) ∧
      (∀v∈trial,Kept W o J (WilsonMeasuredPublicEntranceTrialLamp.leaf E v x) L) ∧
      ∀(v:V)(s:J.Mode)(degree:ℕ)(h:Coefficient (R.family.labels.level degree) (R.family.side f p))
        {σ c Λ δ z κ₀ M C:ℝ},W.Lawful σ c Λ δ z →
        h.Format (o v) R.family.params W → h.remBound (o v) W κ₀ M → h.x=0 → h.regular=0 →
        (∀U,‖h.density (o v) (R.family.localSection degree) W U/(W.eval U:ℂ)‖≤C) →
        let a:=fun i=>if i∈trial then A/w i else cost G (d i) (P).p.threshold*(R.family.labels.level (d i)).coeffSize (q i).x+B i
        let t:=fun i=>if i∈trial then 0 else Real.exp (-(P).p.supportExponent*D i)*B i
        ∀u (uf:u≤f) (Z:Config G (R.family.side u p)),
        ‖held R.family N p (fun U=>account h W U*∏i∈s.val.erase v,Φ i U) uf Z-
         held R.family N p (fun U=>account h W U*∏i∈s.val.erase v,φ i U) uf Z‖≤
          C*WilsonMeasuredPublicEntranceCheapOrder.route a (fun i=>a i+t i) t (s.val.erase v).toList:=by
  classical
  have ap:0≤W.p.supportExponent+2:=by rw [target];linarith
  obtain ⟨lamps,K,_,_,_,rows,_,_,tails⟩:=WilsonMeasuredPublicEntranceCropFamily.original R J cut d ref o
    (fun _=>P) W q D (fun _=>rfl) target fit w wp fees room
  let c:=WilsonMeasuredPublicEntranceCropFamily.fare (N:=N) R d o W q D w B
  obtain ⟨K',ct,L,sale,_,peers,kept,_⟩:=WilsonMeasuredPublicEntrancePeerSelection.original W o J E x trial
    lamps w wp ap base c (fun v=>(rows v).2.1) (fun v=>(rows v).2.2.1) _
    (fun v=>(rows v).2.2.2)
  refine ⟨K',ct,L,sale,peers,kept,?_⟩
  intro v s degree h σ c₀ Λ δ z κ₀ M C law hf hf₁ h0 h1 raw a t u uf Z
  have bounds(i:V):BoundedAt R.family (Φ i) ∧ BoundedAt R.family (φ i) ∧
      (∀U,‖Φ i U‖≤a i) ∧ ∀U,‖Φ i U-φ i U‖≤t i:=by
    by_cases yes:i∈trial
    · have good:=WilsonMeasuredPublicEntrancePeerTests.trial R W o i E x w wp ap base
      have ex:Φ i=(fun U=>(E.log x U).part (J.fire i)):=by funext U;simp [field,yes]
      have ex':φ i=(fun U=>(E.log x U).part (J.fire i)):=by funext U;simp [clipped,yes]
      simpa only [ex,ex',field,clipped,yes,if_true,a,t,sub_self,norm_zero,le_refl,implies_true] using
        (show BoundedAt R.family (fun U=>(E.log x U).part (J.fire i)) ∧
          BoundedAt R.family (fun U=>(E.log x U).part (J.fire i)) ∧
          (∀U,‖(E.log x U).part (J.fire i)‖≤A/w i) ∧ True from ⟨good.1,good.1,good.2,True.intro⟩)
    · have paid:=WilsonMeasuredPublicEntrancePeerTests.trial R W o i (lamps i) () w wp ap (rows i).2.1
      have localEq:=funext ((rows i).2.2.2)
      rw [localEq] at paid
      have ex:Φ i=(q i).exponentialEntry (o i) (R.family.localSection (d i)) P:=by funext U;simp [field,yes]
      have ex':φ i=WilsonMeasuredPublicEntranceCropFamily.value R d o (fun _=>P) q D i:=by funext U;simp [clipped,yes]
      simp only [ex,ex',field,clipped,yes,if_false,a,t]
      exact ⟨WilsonMeasuredPublicEntrancePeerTests.canonical R P o i (q i) (fit i) (fees i),
        paid.1,point R (d i) P (q i) (o i) (fees i),tails i⟩
  have pay:=WilsonMeasuredPublicEntrancePeerTests.hard R W o v h hf hf₁ law h0 h1
  have full:=WilsonMeasuredPublicEntrancePeerTests.dressed R (account h W) pay Φ (fun i=>(bounds i).1) (s.val.erase v)
  have brief:=WilsonMeasuredPublicEntrancePeerTests.dressed R (account h W) pay φ (fun i=>(bounds i).2.1) (s.val.erase v)
  have tail:=WilsonMeasuredPublicEntranceFiredTail.original R cut W same h (o v) h0 h1 raw
    (s.val.erase v).toList (fun U i=>Φ i U) (fun U i=>φ i U) a t
    (fun U i=>(bounds i).2.2.1 U) (fun U i=>(bounds i).2.2.2 U) uf Z
  have diff:=congrFun (linear R.family N p uf _ _ full brief) Z
  simp only [Pi.sub_apply] at diff
  simp only [held,Complex.real_smul,Complex.ofReal_inv,←mul_sub,←diff]
  simpa only [held,prod_map_toList,Pi.sub_def,Pi.sub_apply,Complex.real_smul,Complex.ofReal_inv,mul_sub] using tail

end YM.Integration.WilsonOriginalMicroscopicEntranceHeldCrop
end
