import YM.Integration.WilsonMeasuredPublicEntranceFlatShares
import YM.Integration.WilsonOriginalMicroscopicEntranceHeldLine

/-! All three signed hard-owner shares under the same nonconstant earlier Wilson kernel. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHeldShares
open Function Finset MeasureTheory Lattice RG Wilson
open PhysicalNext PhysicalNext.Repeat Legato WilsonThermometerUnitFilingCoarse
open WilsonMeasuredPublicEntranceFlatLine (films)
open WilsonOriginalMicroscopicEntranceHeldLine (ear)
open WilsonMeasuredPublicEntranceFlatShares (rest owned contact)
open WilsonSeparatedPrefixCanonicalClearConvolution (readingAt)
open private list_price from YM.Integration.WilsonMeasuredPublicEntranceFlatShares
open WilsonMeasuredPublicEntranceOrder
open WilsonMeasuredPublicEntrancePeerShares WilsonMeasuredPublicEntranceCheapOrder
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){V:Type}[DecidableEq V]{N p f b:ℕ}(s:Finset V)
local notation "cfg" => Config G (R.family.side f p)
variable (x y e:V → Config G (R.family.side f p) → ℂ)
theorem original (bf:b ≤ f)(W:Config G (R.family.side b p))(a c z:V → cfg → ℂ)
    (xpay:∀i,BoundedAt R.family (x i))(ypay:∀i,BoundedAt R.family (y i))
    (epay:∀i,BoundedAt R.family (e i))(af:∀i,BoundedAt R.family (a i))
    (cf:∀i,BoundedAt R.family (c i))(zf:∀i,BoundedAt R.family (z i))
    (A C Z:ℝ)(tax:∀m∈shares s.toList,
      ‖readingAt R (N:=N) (owned R s x y e a m) bf W‖ ≤ A ∧
      ‖readingAt R (N:=N) (owned R s x y e c m) bf W‖ ≤ C ∧
      ‖readingAt R (N:=N) (owned R s x y e z m) bf W‖ ≤ Z):
    let F:=contact R s x y e a c z
    Integrable F (prior G _) ∧
      ‖readingAt R (N:=N) F bf W‖ ≤ ((shares s.toList).length:ℝ)*(A+C+Z):=by
  intro F
  have peer (m:Share V)(i:V):BoundedAt R.family (rest R x y e m i):=by
    unfold rest WilsonMeasuredPublicEntranceShareRoster.field WilsonMeasuredPublicEntranceShareRoster.head
    split_ifs
    · exact ypay i
    · exact epay i
    · exact xpay i
  let H (h:V → cfg → ℂ)(hpay:∀i,BoundedAt R.family (h i))(m:Share V):films G (R.family.side f p):=
    ⟨owned R s x y e h m,WilsonMeasuredPublicEntrancePeerTests.dressed R (h m.atName) (hpay _)
      (rest R x y e m) (peer m) (s.erase m.atName)⟩
  let rows (m:Share V):films G (R.family.side f p):=
    weight (fun _=>(1:ℂ)) m • (H a af m-H c cf m-H z zf m)
  have whole (U:cfg):F U=((shares s.toList).map (fun i=>(rows i).val U)).sum:=by
    change WilsonMeasuredPublicEntranceCheapOrder.route _ _ _ _=_
    have issued:=WilsonMeasuredPublicEntrancePeerShares.original (fun i=>x i U) (fun i=>y i U) (fun i=>e i U)
      (fun _=>(1:ℂ)) (fun i=>a i U-c i U-z i U) s.toList
    simp only [one_mul] at issued
    rw [issued]
    apply congrArg List.sum
    apply List.map_congr_left
    intro m chosen
    have prior:=WilsonMeasuredPublicEntranceShareRoster.original s m chosen (fun i=>x i U) (fun i=>y i U) (fun i=>e i U)
    change WilsonMeasuredPublicEntrancePeerShares.weight (fun _=>(1:ℂ)) m*((a m.atName U-c m.atName U-z m.atName U)*peers _ _ _ m)=
      WilsonMeasuredPublicEntrancePeerShares.weight (fun _=>(1:ℂ)) m*(owned R s x y e a m U-owned R s x y e c m U-owned R s x y e z m U)
    rw [prior.2]
    unfold owned rest
    ring
  obtain ⟨paid,file⟩:=WilsonOriginalMicroscopicEntranceHeldLine.original R N p f b bf W (shares s.toList) rows F whole
  refine ⟨paid,?_⟩
  rw [file]
  apply list_price
  intro m present
  obtain ⟨aa,cc,zz⟩:=tax m present
  change ‖ear R N p f b bf W (WilsonMeasuredPublicEntrancePeerShares.weight (fun _=>(1:ℂ)) m • (H a af m-H c cf m-H z zf m))‖ ≤ _
  rw [map_smul,map_sub,map_sub,smul_eq_mul,norm_mul,WilsonMeasuredPublicEntranceShareRoster.sign,one_mul]
  exact (norm_sub_le ..).trans (add_le_add ((norm_sub_le ..).trans (add_le_add aa cc)) zz)

end YM.Integration.WilsonOriginalMicroscopicEntranceHeldShares
end
