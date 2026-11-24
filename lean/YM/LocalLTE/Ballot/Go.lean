import YM.LocalLTE.Ballot.Permit
/-! zip. Runs through before/post Knit docs transparent P. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Vinca
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus MergeProof
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (Y : Hol G){n: Side}
variable (L X:ℕ→Support n)(W:Local.Raw F n)(E:ℕ→ Config G n→ℂ)(o:Site n)(R:Rep G n)
    {σ C Λ δ w z u v a b :ℝ}
local notation "K"=> factor Y B R.p.supportExponent u
local notation "ε"=> hitWidth R.p*w/(Real.sqrt w)
lemma sail (hX:W.Format o L R)(h:Planned.GuardedAtom.Deck W o L R (Real.sqrt w) a b) (S:Berths R.p R.activities X)(S':Berths R.p R.activities (fun i=>joint B o (X i)))(hr: Local.Readable Y B R.p n u)(hc:Dilation.Fills o L X R.p z)(hk:R.Lawful σ C Λ δ w)(hx:0<w)(hf: Local.hitWidth R.p * Real.sqrt w ≤ 1)(he:Patched R.p o X (W.bulk-E) v):
     let t:= Dilation.out L W S; let p:= mint S' t Y
     let E':= Vinca.emit B Y X o R.p.threshold (Dilation.out L W S).seed E; let q:= Vinca.decrement p E'; Patched R.p o X E (z*a+v)∧ E'.Format o Y R∧ p.support=E'.support∧ q.Format o Y R∧ Planned.GuardedAtom.Tab q o R (Real.sqrt w) (K *v) (b+ ε*(z*a)+ ε*(K*(z*a))) ∧ F.coeffSize q.x ≤ K*v :=by
     intro t p E' q
     have hp:= Real.sqrt_pos.mpr hx; have hκ:=Dilation.usualPerm (W:=R) hf hx
     obtain ⟨h₁,h₂,hR,hV,hT⟩:=Dilation.ledger (B:=B) L W S hc hk hx.le hκ.2 hp hX h
     have hW:= Guard.tab_mint S' hR hk hp hr (hT.tare hp hx.le hκ.2 hr hR)
     have hU :Patched R.p o X t.bulk (z*a):=by obtain ⟨i,ha,hb⟩:= hT.bulk; exact ⟨i,hb,fun j=> ⟨hR.regular j,ha j⟩⟩
     obtain ⟨hI,hC,hx',-,hM,hμ,hF⟩:= snapshot B Y X t E o R S' hr hR hU hk (show Patched R.p o X (t.bulk-E) v from he) hW.forced hp hW.second; exact ⟨hI,hx',hC.symm,hM,hμ,hF⟩
end YM.LocalLTE.Vinca
