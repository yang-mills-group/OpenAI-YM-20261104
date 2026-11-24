import YM.OPE.Logarithmic
import YM.Integration.WilsonThermometerWeakRunningRoster

/-! A signed, complete child replacement in the physical logarithmic tree.
The two inputs of the selected child are paid at their own radius and its
sibling at the parent radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakNestedChild
open Function Finset Filter Set Spec Table Extraction OPE OPE.Arboreal OPE.Arboreal.Mountain
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
  {I:Type}[Fintype I]{P:Prescription F.sector.derivatives}

theorem original (bank:LogTrace F P)(s:Arboreal I)(p:I→C.book.Token)
    (a:Mode F.sector.derivatives)(D:I→ℕ)(i:I)(one:s.middle s.zones={i})
    (M δ:ℝ)(mn:0≤M)(dp:0<δ):
    ∃order:ℕ,∀ᶠt:ℝ in 𝓝[>]0,∀(x:I→E4)(r:I→ℝ),r s.root=t→s.Convoy M δ r x→
      s.fee p r s.leaves s.root a.1*
        ‖coalesce P s.leaves x p s.root a-
          ∑v∈bands F.sector.derivatives (D i),
            coalesce P (s.inputs s.zones i) x p i v*
            coalesce P (s.live (s.zones.erase i)) x (update p i (P.letter v)) s.root a‖
        ≤ (Arboreal.prestige s r)^order*(s.ratioAt r i)^(D i+1):=by
  obtain ⟨order,paid⟩:=bank.tickets s p a D M δ mn dp
  refine ⟨order,paid.mono ?_⟩
  intro t issued x r hr h
  have mem:i∈s.middle s.zones:=by simp [one]
  have inside: i∈s.zones:=(mem_erase.mp mem).2
  have ne:i≠s.root:=(mem_erase.mp mem).1
  have border:s.Border s.zones i:=by
    intro j hj anc
    by_cases eq:j=s.root
    · exact (ne ((eq ▸ anc).excess)).elim
    · have jmem:j∈s.middle s.zones:=mem_erase.mpr ⟨eq,hj⟩
      simpa only [one,Finset.mem_singleton] using jmem
  have remains:s.middle (s.redact s.zones i)=∅:=by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    rw [Arboreal.middle,s.redact_one border] at hj
    obtain ⟨nr,ni,hz⟩:=show j≠s.root ∧ j≠i ∧ j∈s.zones from by simpa using hj
    have hmem:j∈s.middle s.zones:=mem_erase.mpr ⟨nr,hz⟩
    exact ni (Finset.mem_singleton.mp (one ▸ hmem))
  have calcRow:= (issued x r hr h order le_rfl).combination
  rw [Nest.contracted P border mem x p a D] at calcRow
  simp_rw [Nest.staging P x a (s.redacted s.Action mem) remains D, s.redact_one border] at calcRow
  have wage:= h.sizes.fee_pos (b:=s.leaves) p a.1 s.initial
  have total:= mul_le_mul_of_nonneg_left calcRow wage.le
  rw [Arboreal.listPrice,Arboreal.grace,one,sum_singleton] at total
  calc _≤_:=total
       _=_:=by
         rw [←mul_assoc,←mul_assoc,mul_comm (s.fee ..) (s.tariff ..),h.sizes.reward_eq a.1 p,one_mul]

end YM.Integration.WilsonThermometerWeakNestedChild
end
