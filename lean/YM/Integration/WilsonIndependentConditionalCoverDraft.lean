import YM.Integration.WilsonIndependentConditionalDraftRows

/-! Fubini for a whole sourced angular tensor. Absolute summability is on
its actual deposited coordinates before the convolution. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalCoverDraft
open RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet Function
open WilsonIndependentConditionalDraftRows
open scoped Classical BigOperators
variable {I:Type}{K:Layer I I}{r:ℕ}{T:Packet I r}{C:ℝ}

theorem expanded (bound:1≤C)(wage:∀x y,|K x y|≤C)(price:Summable (fun y=>‖T y‖))
    (l:List (Fin r))(uniq:l.Nodup)(z:Tuple I r):
    drawing T K l z=∑' y,wires K l.toFinset z y*T y:=by
  classical
  induction l generalizing z with
  | nil=>
    simp only [drawing,List.toFinset_nil,empty]
    symm;rw [tsum_eq_single z]
    · simp
    · intro y ne;simp [ne]
  | cons a l ih=>
    obtain ⟨fresh,nodup⟩:=List.nodup_cons.mp uniq
    let W:Tuple I r→ℝ:=fun y=>wires K (insert a l.toFinset) z y*T y
    have cash:Summable W:=paid bound wage price _ _
    let f:Tuple I r→I:=fun y=>y a
    have leaf (y:I):K (z a) y*(∑' x,wires K l.toFinset (update z a y) x*T x)=
          ∑' x:(f ⁻¹' {y}),W x:=by
      rw [←tsum_mul_left,tsum_subtype]
      apply tsum_congr;intro x
      rw [←mul_assoc,single K (by simpa using fresh)]
      by_cases eq:x a=y
      · simp [eq,W,Set.indicator,f]
      · simp [eq,W,Set.indicator,f]
    simp only [drawing,ray,swivel,List.toFinset_cons]
    calc
      _=∑' y, ∑' x:(f ⁻¹' {y}),W x:=by
        apply tsum_congr;intro y;rw [ih nodup];exact leaf y
      _=∑' y,W y:=(cash.hasSum.tsum_fiberwise f).tsum_eq

theorem original (bound:1≤C)(wage:∀x y,|K x y|≤C)(price:Summable (fun y=>‖T y‖)):
    draft K T=Packet.symmetry (fun z=>∑' y,(∏ i,K (z i) (y i))*T y):=by
  classical
  unfold draft
  apply congrArg Packet.symmetry
  funext x;rw [expanded bound wage price _ (List.nodup_finRange r)]
  simp [show (List.finRange r).toFinset=Finset.univ by ext;simp,full]

end YM.Integration.WilsonIndependentConditionalCoverDraft
