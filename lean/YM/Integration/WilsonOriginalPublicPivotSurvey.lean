import YM.Integration.WilsonOriginalPublicFigurePosition

/-! Recover the actual two fitted decks under a finite change of bare frame.
The genuine position equations and their elected branch supply uniqueness. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace YM.Integration.WilsonOriginalPublicPivotSurvey
open Filter Function PowerSeries
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Structure1 Maxwell
open MS MS.Book MS.Book.Program WilsonOriginalPublicFigurePosition
open scoped Classical BigOperators Topology
variable {G:Gauge} {d:ℕ}

theorem equivariant {A:Screen G d} (D:Fray A) (H:A.Prepared) (P:Reports G d)
    (S:Guard G d)(formal:Formal S)(one:constantCoeff S=1)(paid:Fray.Executed D H P):
    S*deck (D.Lays H (realm S P))=deck (D.Lays H P):=by
  let Q:=realm S P
  let v:=D.Lays H Q
  let a:=D.Lays H P
  have same:Q 0=P 0:=by unfold Q;rw [rest,coeff_zero_eq_constantCoeff_apply,one];rfl
  have next:=Fray.no_reset D H paid (Q:=Q) same.symm
  obtain ⟨k,hk⟩:=(Formal.product (Y:=deck v) formal next.1).actions
  have first:k 0=a 0:=by
    have e:stand (k 0)=stand (a 0):=by
      rw [←const_deck,←hk,map_mul,one,one_mul,const_deck]
      unfold a v
      rw [Fray.leads,Fray.leads,same]
    apply Subtype.ext
    ext1 p; exact add_left_cancel (DFunLike.congr_fun e p)
  have reports:realm (deck k) P=realm (deck v) Q:=by rw [←hk,←parlance]
  have solved:A.Solved k P:=fun q=>by rw [reports];exact next.2.1 q
  have unique:=A.shift_unique P _ _ first.symm paid.2.1 solved paid.2.2.1
  exact hk.trans (congrArg deck unique.symm)

theorem cancel {A:Screen G d} (D:Fray A) (H:A.Prepared) (P:Reports G d)
    (S T:Guard G d) (formal:Formal S)(one:constantCoeff S=1)(inv:T*S=1)(paid:Fray.Executed D H P)
    (B:Guard G d) (orig:deck (D.Lays H P)*B=1):
    ∃C:Guard G d,Formal C ∧ C*deck (D.Lays H (realm S P))=1 ∧
       deck (D.Lays H (realm S P))*C=1 ∧ B=C*T:=by
  have same:realm S P 0=P 0:=by rw [rest,coeff_zero_eq_constantCoeff_apply,one];rfl
  have next:=Fray.no_reset D H paid same.symm
  obtain ⟨C,ok,cz,zc⟩:=reversal_exists next.1
  refine ⟨C,ok,cz,zc,?_⟩
  have z:=equivariant D H P S formal one paid
  calc
    B=1*B:=by rw [one_mul]
    _=(C*deck (D.Lays H (realm S P)))*B:=by rw [cz]
    _=(C*(T*S)*deck (D.Lays H (realm S P)))*B:=by rw [inv,mul_one]
    _=C*T*(deck (D.Lays H P)*B):=by rw [←z];simp only [mul_assoc]
    _=C*T:=by rw [orig,mul_one]

/-- All subfaces use this same actual compensated inverse at the finite mesh. -/
theorem original (W:Initialize G)(V:Store G)(d:ℕ):
    ∀ᶠ m in Front,∀(team:ℕ→Plan)(θ:ℝ),
    let raw:=clock team θ (batch W m d)
    let Z:=deck ((V.survey d).Lays (V.prepared d) raw)
    ∀S T:Guard G d, Formal S → constantCoeff S=1 → T*S=1 →
    ∃C:Guard G d,Formal C ∧ C*deck ((V.survey d).Lays (V.prepared d) (realm S raw))=1 ∧
      deck ((V.survey d).Lays (V.prepared d) (realm S raw))*C=1 ∧
      Z*(C*T)=1 ∧ C*T*Z=1 ∧
      (∀q,coeff q (C*T) (leaf G d)=if q=0 then leaf G d else 0) ∧
      ∀n (φ:Test n)(p:Fin n → Sec G d)(s:Finset (Fin n)),
       YM.FVAAlt2.Lobby.redo team θ (said (batch W m d) φ (missing p s))=
         ∑b:Fin n→Dime G d,said (booked V W m d team θ) φ (fun i=>dime G d (b i))*
           ∏i,tax (C*T) (missing p s i) (b i):=by
  filter_upwards [(V.nested_solution W d frontier).2,WilsonOriginalPublicFigurePosition.original V W d] with m known law
  have works:Fray.Executed (V.survey d) (V.prepared d) (batch W m d):=
    ⟨known.1.1,known.1.2.1,known.1.2.2.2.2.2⟩
  intro team θ raw Z S T formal one inv
  have legal:Fray.Executed (V.survey d) (V.prepared d) raw:=
    Fray.no_reset (V.survey d) (V.prepared d) works (clock_ground ..).symm
  obtain ⟨B,_,zb,bz,unit,_,reading⟩:=law team θ
  obtain ⟨C,ok,cz,zc,eq⟩:=cancel _ _ raw S T formal one inv legal B zb
  exact ⟨C,ok,cz,zc,eq ▸ zb,eq ▸ bz,eq ▸ unit,eq ▸ reading⟩

end YM.Integration.WilsonOriginalPublicPivotSurvey
end
