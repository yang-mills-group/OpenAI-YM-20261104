import YM.Integration.WilsonMacroscopicRichSignedAmplitude

/-! The paid two-site exterior keeps its genuine full support and both
near coordinates. Its room margins precede the two moving radii. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkSupport
open Function Filter Set RG17 OPE OPE.Orbits OPE.Arboreal
open WilsonMacroscopicRichTestGeometry WilsonMacroscopicRichMovingPlane
open scoped Classical Topology
variable {n:ℕ}
def one : Fin 1 ≃ Unit :=
  ⟨fun _=>(),fun _=>0,fun _=>Subsingleton.elim _ _,fun _=>Subsingleton.elim _ _⟩

private lemma joins {r t:ℝ}{x:Points n}{z:Points 2}(safe:placed r t x (relative z)∈conf (n+1)):
    Injective (beside (posed r x) (sole (t • relative z 0))):=by
  let reindex:Fin n ⊕ Unit ≃ Fin (n+1):=(Equiv.sumCongr (Equiv.refl (Fin n)) one.symm).trans finSumFinEquiv
  have linked:beside (posed r x) (sole (t • relative z 0)) = fun i=>placed r t x (relative z) (reindex i):=by
    funext i;rcases i with i|i
    · change r • x i = Fin.append (fun i=>r•x i) (fun j=>t•relative z j) (Fin.castAdd 1 i)
      rw[Fin.append_left]
    · change t • relative z 0 = Fin.append (fun i=>r•x i) (fun j=>t•relative z j) (Fin.natAdd n 0)
      rw[Fin.append_right]
  rw[linked]; exact safe.comp reindex.injective

private lemma solo {z:E4}(nz:z≠0):Injective (beside (sole (0:E4)) (sole z)):=by
  rintro (i|i) (j|j) e <;> (first|exact congrArg _ (Subsingleton.elim _ _)|exact (nz e.symm).elim|exact (nz e).elim)

theorem original (K:Set (Points n))(compact:IsCompact K)(spread:K⊆conf n)(φ:Test 2):
    ∃ M δ η:ℝ,0≤M ∧ 0<δ ∧ 0<η ∧ ∀(r t:ℝ),0<r → 0<t → r/t≤η → ∀x∈K,∀z∈tsupport φ,
      let far:=relative z 0
      (∀i,‖x i‖≤M) ∧ ‖far‖≤M ∧ 2*δ≤‖far‖ ∧ (∀i j,i≠j → δ≤‖x i-x j‖) ∧
      Injective (beside (posed r x) (sole (t • far))) ∧
      Injective (beside (sole (0:E4)) (sole (t • far))) ∧ placed r t x (relative z)∈conf (n+1):=by
  obtain ⟨a,b,a0,b0,near⟩:=roomCosts compact spread
  obtain ⟨c,d,c0,d0,outer⟩:=roomCosts φ.hasCompactSupport φ.tsupport_subset
  obtain ⟨η,η0,safe⟩:=clearance K compact spread φ
  refine ⟨max a (2*c),min b (d/2),η,a0.trans (le_max_left _ _),lt_min b0 (half_pos d0),η0,?_⟩
  intro r t rp tp pair x hx z hz
  have nx(i:Fin n):‖x i‖≤a:=by simpa [posed] using (near 1 one_pos x hx).span i
  have nz(i:Fin 2):‖z i‖≤c:=by simpa [posed] using (outer 1 one_pos z hz).span i
  have gap(i j:Fin n)(ne:i≠j):b≤‖x i-x j‖:=by simpa [posed] using (near 1 one_pos x hx).spaced i j ne
  have far:d≤‖relative z 0‖:=by simpa [posed,relative] using (outer 1 one_pos z hz).spaced 1 0 (by decide)
  have width:‖relative z 0‖≤2*c:=by
    change ‖z 1-z 0‖≤2*c; linarith [norm_sub_le (z 1) (z 0),nz 0,nz 1]
  have separated:=safe r t rp tp pair x hx z hz
  have rel:relative z 0≠0:=norm_pos_iff.mp (d0.trans_le far)
  refine ⟨fun i=>(nx i).trans (le_max_left _ _),width.trans (le_max_right _ _),
    ?_,fun i j ne=>(min_le_left _ _).trans (gap i j ne),joins separated,solo (smul_ne_zero tp.ne' rel),separated⟩
  linarith [min_le_right b (d/2)]

end YM.Integration.WilsonPublicForkSupport
