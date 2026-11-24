import YM.Integration.WilsonCenteredFourOutputSensor

/-! On each supported smooth joint test the positive coordinate of the
whole deposited packet is the actual integral of the reader's coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourOutputDeposit
open Function Set Filter MeasureTheory Spec Extraction Table OPE OPE.Orbits RG17
open WilsonCenteredFourOutputSensor
open scoped Classical BigOperators Topology
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book}
  (F:Final C f S) (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

theorem actual {n:ℕ} {d:Fin n→ℕ} (v:Labels S d) (r:ℝ) (ψ:Test n) (c:Q.channels 4)
    (clear:∀x∈tsupport ψ,∀j≤4,orbitMargin Q.port j (posed r x) 0):
    grade F Q c (RG17.basket Q 4 v r ψ) = ∫x:Points n,ψ x*Q.coef 4 c (posed r x) v 0:=by
  have paid:=RG17.basket_int Q v 4 ψ clear
  unfold RG17.basket
  rw [←(grade F Q c).integral_comp_comm paid]
  simp only [map_smul,WilsonCenteredFourOutputSensor.packet,smul_eq_mul]

theorem original (fac:Services C f S) {K:Set (Points 2)} (compact:IsCompact K)
    (away:K⊆conf 2) :
    ∀ᶠ r in RG17.home,∀ (v:Fin 2→S.Field 4) (c:Q.channels 4) (ψ:Test 2),tsupport ψ⊆K →
      grade F Q c (RG17.basket Q 4 (d:=fun _:Fin 2=>4) v r ψ)=
      ∫x:Points 2,ψ x*Q.coef 4 c (d:=fun _:Fin 2=>4) (posed r x) v 0:=by
  obtain ⟨M,η,Mn,ηp,placed⟩:=RG17.roomCosts compact away
  let w:Labels S (fun _:Fin 0=>0):=Fin.elim0
  let zero:Labels S (fun _:Fin 2=>4):=fun _=>0
  have safe:=profile_scope (ε:=1) F Q fac zero w Mn ηp (show (0:ℝ)<1 by norm_num) zero_lt_one 4
  filter_upwards [safe,RG17.positiveLength] with r padded rp v c ψ support
  apply actual F Q v r ψ c
  intro x hx k hk
  let y:Fin 0→E4:=Fin.elim0
  have exterior:ClearOf 0 y 1:=⟨fun i=>i.elim0,fun i=>i.elim0⟩
  have room: ((posed r x,(0:E4),y):Loc (Fin 2) (Fin 0)) ∈guardZone F Q 4:=
    (padded.2 _ (Set.mem_setOf.mpr ⟨placed r rp x (support hx),exterior⟩)).1
  exact room.1 k hk

end YM.Integration.WilsonCenteredFourOutputDeposit
