import YM.Integration.WilsonMeasuredPublicEntranceOwnerSale
import YM.Integration.WilsonSeparatedPrefixCanonicalForced

/-! Original rooted flow and native one-divisor payment for the sole marked
canonical hard address among arbitrary regular spectators. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceOwnerFlags
open Function Finset Lattice Wilson RG Source Labels Marker Extra.Histories Push.Local
open MergeProof MergeProof.Accent Push.GridApprox.Nil
open WilsonMeasuredPublicEntranceOwnerGas
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{d:ℕ}{F:Labels.Frame G d}{V:Type}[Fintype V][DecidableEq V]{J:Census V}
variable {P:Rep G n}(o:V→Site n)(q:Coefficient F n)(v:V)

omit [Fintype V] in
theorem vacant (t:ℝ)(b:Box n):Flow o b (fun _ : Config G n=> (0:Poly J)) t:=by
  exact ⟨⟨fun _ _ _ _=>rfl,fun _ _=>rfl,fun _=>measurable_const,fun _ _ _=>rfl⟩,
    fun _ h=>False.elim (h rfl)⟩

omit [Fintype V] in
theorem original (w:V→ℝ)(wp:∀i,0<w i){α:ℝ}(e0:0≤P.p.supportExponent)(le:α≤P.p.supportExponent)
    {A:Hol G}{κ M:ℝ}(fit:q.Format (o v) A P)(fee:q.remBound (o v) P κ M)(i:V):
    let h:=fun b U=>Poly.send (J.fire i) (selected P q v i b U)
    Towed w Prod.fst h P.p.B α (if i=v then w v*(κ*M) else 0) ∧ ∀b,Flow o b (h b) P.p.threshold:=by
  intro h
  have funded:=WilsonSeparatedPrefixCanonicalForced.original (J:=J) v q fit w wp e0 fee
  by_cases live:i=v
  · subst i
    refine ⟨?_,?_⟩
    · simpa only [h,selected,if_pos rfl,if_true] using funded.1.shrink le le_rfl wp
    · simpa only [h,selected,if_pos rfl,if_true] using funded.2
  · have paid:=WilsonSeparatedPrefixCanonicalFares.scale funded.1 (0:ℂ)
    have zero:Towed w Prod.fst (fun (_:Box n)(_ : Config G n)=> (0:Poly J)) P.p.B P.p.supportExponent 0:=by
      simpa only [zero_smul,norm_zero,zero_mul] using paid
    refine ⟨?_,?_⟩
    · simpa [h,selected,live] using zero.shrink le le_rfl wp
    · simpa [h,selected,live] using WilsonMeasuredPublicEntranceOwnerFlags.vacant (G:=G) (J:=J) o P.p.threshold

end YM.Integration.WilsonMeasuredPublicEntranceOwnerFlags
end
