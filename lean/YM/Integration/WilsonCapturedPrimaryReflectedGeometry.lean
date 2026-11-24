import YM.Integration.WilsonReflectedMicroscopicSites
import YM.Integration.WilsonCapturedPrimarySupportedHalo
import YM.OPE.Loom.Tail

/-! Distinct original reflected cubes and the true compact children inside them.
The one connected capturing ball and the separation of distinct copies use the
actual odd-block parents at every admitted ultraviolet cutoff and period. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryReflectedGeometry
open Filter Finset Lattice Wilson RG Source PhysicalNext.Repeat.Legato Next.Rank
open Push.GridApprox MergeProof MergeProof.Ribbons MergeProof.Ribbons.ManyCopies
open Extra.Histories Motion Extra.Multi Pressure Marker RG12 Cells Extraction Table
open WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetJoint WilsonReflectedMicroscopicSites
open scoped Classical BigOperators Topology
set_option quotPrecheck false
variable {G:Gauge} (R:Run G) (simple:G.Simple)
variable {N per J b:ℕ}
local notation "CF" => R.family
local notation "B" i:max => ((CF).path.levels.budget i).B
local notation "E" => Mix.camp (CF) per J
local notation "P" => hands (CF) per J

theorem shell (J:ℕ) : ∀ᶠ b:ℕ in atTop, J ≤ b ∧ ∀ per (jb:J ≤ b),
    (B b)^2+1+2*(B b)  ≤  ((CF).S.toDepth jb per).count.val := by
  filter_upwards [OPE.Loom.sail (C:=CF) 1 J,eventually_ge_atTop J] with b bought age
  refine ⟨age,fun per jb=>?_⟩
  have size : B b  ≤  OPE.Loom.stride (CF) 50 b := by
    unfold OPE.Loom.stride
    exact (Nat.le_mul_of_pos_right _ (by omega)).trans (Nat.le_add_right ..)
  have fee:=bought per jb
  rw [one_mul] at fee
  omega

theorem distance {I:Type} (z:I → Site ((CF).side N per)) (jb:J ≤ b) (live:b ≤ N)
    (h:∀v,separation (((CF).S.toDepth live per).parent (z v)) 0  ≤  B b)
    (a:Site ((CF).side J per)×I) :
    separation (site R (J:=J) z b a) (E b a.1)  ≤  B b := by
  rw [transformed R z jb live a]
  change separation ((P a.1).1.act (WilsonThermometerOwnOffsetNectar.location R (z a.2) b) + E b a.1) (E b a.1)  ≤  _
  have iso : separation ((P a.1).1.act (WilsonThermometerOwnOffsetNectar.location R (z a.2) b) + E b a.1)
      ((P a.1).1.act (0:Site ((CF).side b per)) + E b a.1) =
      separation (WilsonThermometerOwnOffsetNectar.location R (z a.2) b) 0 := by rw [separation_translate,separation_signed]
  have home : separation (WilsonThermometerOwnOffsetNectar.location R (z a.2) b) 0  ≤  B b := by simpa [WilsonThermometerOwnOffsetNectar.location,WilsonThermometerOwnOffsetTale.site,live] using h a.2
  simpa using iso.le.trans home

theorem oneBall {I:Type} (z:I → Site ((CF).side N per)) (jb:J ≤ b) (live:b ≤ N)
    (h:∀v,separation (((CF).S.toDepth live per).parent (z v)) 0  ≤  B b)
    (a:Site ((CF).side J per)) (i j:I) :
    coverNumber (B b) ({site R (J:=J) z b (a,i),site R (J:=J) z b (a,j)}:Support _)  ≤  1 := by
  let center:=E b a
  suffices bill : covers (B b) ({site R (J:=J) z b (a,i),site R (J:=J) z b (a,j)}:Support _) {center} by
    simpa using Corona.list_cost (B b) bill
  constructor
  · intro x hx
    refine halo_spec.mpr ⟨center,mem_singleton_self _,?_⟩
    rw [separation_comm]
    rcases mem_insert.mp hx with rfl|hx
    · exact distance R z jb live h (a,i)
    obtain rfl:=mem_singleton.mp hx
    exact distance R z jb live h (a,j)
  · apply Corona.ship_halo
    intro x hx y hy
    have a':x=center:=mem_singleton.mp hx
    have b':y=center:=mem_singleton.mp hy
    subst x;subst y;exact .refl

include simple in
theorem cross {I:Type} (z:I → Site ((CF).side N per)) (jb:J ≤ b) (live:b ≤ N)
    (h:∀v,separation (((CF).S.toDepth live per).parent (z v)) 0  ≤  B b)
    (size:(B b)^2+1+2*(B b)  ≤  ((CF).S.toDepth jb per).count.val)
    {i:ℕ} (outerAge:b ≤ i) (valid:i ≤ N) :
    ∀a c:Site ((CF).side J per)×I,a.1 ≠ c.1  → 
      (B i)^2 < separation (site R (J:=J) z i a) (site R (J:=J) z i c) := by
  intro a c diff
  have cent : ((CF).S.toDepth jb per).count.val  ≤  separation (E b a.1) (E b c.1) := by
    rw [elev (CF) J per b jb,elev (CF) J per b jb,Station.both]
    exact Nat.le_mul_of_pos_right _ (Station.separation_pos a.1 c.1 diff)
  have one:=distance R z jb live h a
  have two:=distance R z jb live h c
  have ac:=separation_triangle (E b a.1) (site R z b a) (E b c.1)
  have ac':=separation_triangle (site R z b a) (site R z b c) (E b c.1)
  rw [separation_comm (E b a.1) (site R z b a)] at ac
  have base : (B b)^2 < separation (site R z b a) (site R z b c) := by omega
  let Z:=(CF).S.toDepth outerAge per
  have exp:= (OPE.Log.Trunk.Canvas.expands (C:=CF) (site R (J:=J) z i a) (site R z i c) outerAge).1
  have collapse (v:Site ((CF).side J per)×I) :
      Z.parent (site R (J:=J) z i v)=site R z b v :=
    WilsonThermometerOwnOffsetGeometry.placed R (tip R (J:=J) z) outerAge valid v
  rw [collapse,collapse] at exp
  have scaled:=Nat.mul_le_mul_left Z.count.val base
  rw [Nat.mul_succ] at scaled
  have uniform := gap_comp (CF) per b i (WilsonThermometerOwnOffsetGeometry.production R simple) outerAge
  exact Nat.lt_of_le_of_lt uniform (Nat.lt_of_add_lt_add_right (scaled.trans_lt exp))

include simple in
theorem original (J:ℕ) (φ:Test 3) : ∃t>0,∀r:ℝ,0<r  →  r ≤ t  → 
    let b:=WilsonCapturedPrimarySupportedHalo.date R r
    J ≤ b ∧ ∀N per (_live:b ≤ N) (z:Fin 3 → Site ((CF).side N per)),
    WilsonSeparatedOriginalThermometerCells.weight φ
      (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r (N,per)) z  ≠  0  → 
    (∀a:Site ((CF).side J per),∀i j:Fin 3,coverNumber (B b)
       ({site R (J:=J) z b (a,i),site R (J:=J) z b (a,j)}:Support _)  ≤  1) ∧
    ∀i,b ≤ i  →  i ≤ N  →  ∀a c:Site ((CF).side J per)×Fin 3,a.1 ≠ c.1  → 
       (B i)^2 < separation (site R z i a) (site R z i c) := by
  obtain ⟨T,hT,halo⟩:=WilsonCapturedPrimarySupportedHalo.dated R simple φ
  obtain ⟨M,sail⟩:=eventually_atTop.mp (shell R J)
  refine ⟨min T ((CF).S.a M),lt_min hT ((CF).S.a_pos M),?_⟩
  intro r rp small
  let b:=WilsonCapturedPrimarySupportedHalo.date R r
  have mesh:=small.trans (min_le_right ..)
  have bracket:= WilsonCloseCaptureDate.bracket (CF).S rp (mesh.trans ((CF).S.strictAnti.antitone (Nat.zero_le M)))
  have age : M ≤ b := by
    by_contra! early
    exact (not_lt_of_ge ((CF).S.strictAnti.antitone (Nat.succ_le_of_lt early))) (bracket.1.trans_le mesh)
  obtain ⟨jb,counts⟩:=sail b age
  refine ⟨jb,?_⟩
  intro N per live z paid
  have h:=halo r rp (small.trans (min_le_left ..)) N per live z paid
  exact ⟨oneBall R z jb live h,fun _ outerAge valid=>cross R simple z jb live h (counts per jb) outerAge valid⟩

end YM.Integration.WilsonCapturedPrimaryReflectedGeometry
