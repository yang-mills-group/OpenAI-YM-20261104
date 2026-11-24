import YM.Integration.WilsonPositionProgramPublicFourFrame
import YM.Integration.WilsonPositionProgramPublicWickGram

/-! The four signed physical rows of one measured public preframe determine
the difference of the two submitted public coefficient columns. All four
independent readings use the very same reflected Gram and numerical source. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicFourPrice
open Filter Function Extraction Table Spec PhysMS Lattice
open Source Labels Maxwell Maxwell.Free MS MS.Menus
open Local.Physical WilsonThermometerUnitFilingFourSquare
open WilsonPositionProgramPublicContrast WilsonPositionProgramPublicStations
open WilsonPositionProgramPublicWickGram
open scoped Topology BigOperators Classical
variable {I J : Type*} [Fintype I] [Fintype J]

def difference (h:Bool→Bool→ℂ) := (h false false-h false true)-(h true false-h true true)

private theorem left_sub (a b:I→ℂ) (c:J→ℂ) (p:I→J→ℂ) :
    assay (a-b) c p = assay a c p-assay b c p := by
  simp only [WilsonPositionProgramPublicContrast.assay,Pi.sub_apply,star_sub,sub_mul,Finset.sum_sub_distrib]

private theorem right_sub (a:I→ℂ) (b c:J→ℂ) (p:I→J→ℂ) :
    assay a (b-c) p = assay a b p-assay a c p := by
  simp only [WilsonPositionProgramPublicContrast.assay,Pi.sub_apply,mul_sub,sub_mul,Finset.sum_sub_distrib]

theorem common (u:Bool→I→ℂ) (v:Bool→J→ℂ) (p:I→J→ℂ) :
    assay (u false-u true) (v false-v true) p = difference (fun b c=>assay (u b) (v c) p) := by
  simp only [left_sub,right_sub,difference]
  ring

theorem invoice {e:ℝ} (h q:Bool→Bool→ℂ) (paid:∀b c,‖q b c-h b c‖≤e) :
    ‖difference q‖≤‖difference h‖+4*e := by
  let δ (b c:Bool):=q b c-h b c
  have subtract : difference q-difference h=difference δ := by dsimp [difference,δ]; ring
  have pair (b:Bool) : ‖δ b false-δ b true‖≤e+e := (norm_sub_le ..).trans (add_le_add (paid ..) (paid ..))
  have bill : ‖difference δ‖≤4*e := by
    apply (norm_sub_le ..).trans
    linarith [pair false,pair true]
  have bound := norm_sub_norm_le (difference q) (difference h)
  rw [subtract] at bound
  linarith

variable {G:Gauge} {C:Family G} {S:Table C.book} {f:Extraction.Order}
    {l:Filter (ℕ×ℕ)} [l.NeBot] {d:ℕ} (F:Final C f S) (signed:Signed)
    {v:I→S.Field d} (arm:(i:I)→Bool→Arm C S l d (v i)) (test:I→I→Test 2)

def heard (w:I→ℂ) (z:ℕ×ℕ) (a b:Bool) :=
  assay w w (fun i j=>corner F signed arm arm test z i j a b)

theorem original {B:Local.Physical.Deck G} {h:ℕ} {K:Type} [Fintype K]
    (axis:Axis) (leg:K→Glyph B h) (each:Injective leg) (order:l≤f.fuse) :
    ∃ k δ:ℝ, 0<k ∧ 0<δ ∧ ∀ (w:ℕ×ℕ→I→ℂ) (u:ℕ×ℕ→Bool→K→ℂ) (p:ℕ×ℕ→K→K→ℂ)
      (A e:ℝ), (∀ᶠ z in l,charge (w z)≤A) →
      (∀ᶠ z in l,‖p z-reading axis (nodes axis) leg‖≤δ) →
      (∀ᶠ z in l,∀a b,‖assay (u z a) (u z b) (p z)-heard F signed arm test (w z) z a b‖≤e) →
      ∀ η:ℝ, 0<η → ∀ᶠ z in l, k*‖u z false-u z true‖^2≤4*e+η := by
  obtain ⟨k,δ,hk,hδ,stable⟩:=WilsonPositionProgramPublicWickGram.original axis leg each
  refine ⟨k,δ,hk,hδ,?_⟩
  intro w u p A e bound mesh fees η hη
  have eq (z:ℕ×ℕ) : difference (heard F signed arm test (w z) z) =
      assay (w z) (w z) (table F signed arm arm test z) := by
    unfold difference heard
    simp only [← WilsonPositionProgramPublicQuadratic.subtracted]
    rfl
  have small:= ((WilsonPositionProgramPublicContrast.original F signed arm arm test order w w bound bound).norm).eventually
    (gt_mem_nhds (show ‖(0:ℂ)‖<η by simpa using hη))
  filter_upwards [mesh,fees,small] with z hmesh hfees hz
  have hl:=stable (p z) hmesh (u z false-u z true)
  rw [common] at hl
  have pay:=invoice (heard F signed arm test (w z) z) (fun a b=>assay (u z a) (u z b) (p z)) hfees
  have final : ‖difference (heard F signed arm test (w z) z)‖<η := by rw [eq]; exact hz
  linarith

end YM.Integration.WilsonPositionProgramPublicFourPrice
