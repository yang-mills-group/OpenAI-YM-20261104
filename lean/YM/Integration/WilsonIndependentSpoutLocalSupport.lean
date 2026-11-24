import YM.Integration.WilsonIndependentSpoutPaidAddon

/-! Pointwise support of the actual selected positive-order primitive tensor
on each of its original incoming links, before a sum over translates. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutLocalSupport
open PowerSeries Lattice RG RegulatorIR RegulatorIR.Binding RegulatorIR.Geometry
open RegulatorIR.Geometry.Field RegulatorIR.Prim RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.Diagram RegulatorIR.Diagram.Formal RegulatorIR.Oracle Tree
open scoped Classical BigOperators
variable {I J:Type}{F:Micro I}{T:Orders I}{k:ℕ}{s:ℝ}

theorem pixels (i:J↪I)[Fintype J](h:Lab k s F T)
    (same:∀t x y,x ∘ i=y ∘ i→F t x=F t y)(e r:ℕ)(x:Tuple I r)
    (a:Fin r)(away:x a∉Set.range i):T e r x=0:=by
  rcases Nat.eq_zero_or_pos e with hz|he
  · subst e;rw [h.awake];rfl
  let R:Ranked I:=fun l=>offer i (crop i (T e l))
  have bound:Within (e+k) R:=by
    intro l nz
    apply h.scope_ e l
    intro zero
    apply nz
    funext z
    simp [R,zero,crop,offer,Stalk.collect]
  have sameR:T e=R:=by
    apply guessed (h.scope_ e) bound (h.smooth e) (fun r=>offer_symm i _ (crop_symm i _ (h.smooth e r)))
    intro v
    have hv:flank F v=flank F (dilute i (v∘i)):=by
      funext t
      apply same
      funext z
      change t*v (i z)=t*dilute i (v∘i) (i z)
      rw [dilute_here]
      rfl
    rw [flute v i (fun l=>crop i (T e l)),←cheap (v∘i) i (T e) (e+k),h.figures _ he,h.figures _ he,hv]
  rw [sameR]
  apply offer_zero i
  rintro ⟨y,hy⟩
  exact away ⟨y a,congr_fun hy a⟩

end YM.Integration.WilsonIndependentSpoutLocalSupport
