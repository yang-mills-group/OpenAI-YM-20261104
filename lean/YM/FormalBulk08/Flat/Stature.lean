import YM.FormalBulk08.Flat.Pouch

/-!
Path and gauge projection for tree slices as actual `Row`s with ANY
prepaid width (these objects independent of the cutoff). Some bills are
intentionally wasteful post-block. Commit equivalence `splitting` and don't
hide an equality only on one torus. This will supply rate also on active
conditional Gaussian inverse subtracts on the cover.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Flat
open Filter Set Function Lattice Laurent Bloch Exterior Precision RG Next.Free UVExtension.Free Work.F08 Stationary Tree
open scoped Topology BigOperators Matrix
variable {G : Gauge} {P : Patch}

namespace Lodge

def footRow (G : Gauge) (P : Patch) (K : KernelChoices) (T : Lodge P) := minusRows (composeRows (deposit (hikes G P K T)) (cutRow G P.L))
    (composeRows (deposit (fatherStick G P)) (plusRows (composeRows (deposit (decorated G P)) (cutRow G P.L)) (deposit (coversRow P G))))
-- d to gradient (fine grouped)
def stepRow (G : Gauge) (P : Patch) := onBlocks _ _ P.L (shadedRows G (cobound 0))

def marchRow (G : Gauge) (P : Patch) (K : KernelChoices) (T : Lodge P) := plusRows (cutRow G P.L) (composeRows (stepRow G P) (footRow G P K T))

def closeRow (G : Gauge) (P : Patch) (K : KernelChoices) (T : Lodge P) := composeRows (touchRow T G) (marchRow G P K T)

open scoped Classical
lemma foot_staged (G : Gauge) (T : Lodge P) (K : KernelChoices) (η : ℝ) (hη : 0<η) : ∃ C,
    (footRow G P K T).strip η C ∧
    ∀ c : Side, let S:=primary P K c; (footRow G P K T).acts c=repackM (unitSplit G S 0) (clothe G S) (lead G S T.forest) := by
  let B:= cutRow G P.L
  let H:= deposit (hikes G P K T); let R:=deposit (fatherStick G P)
  let Y:= deposit (decorated G P); let D:=deposit (coversRow P G)
  obtain ⟨_,_,hH⟩:=deposit_price (hikes G P K T) η
  obtain ⟨_,_,hR⟩:=deposit_price (fatherStick G P) η
  obtain ⟨_,_,hY⟩:=deposit_price (decorated G P) η
  obtain ⟨_,_,hD⟩:=deposit_price (coversRow P G) η
  have hB:= cut_pay G P.L η
  let I:= composeRows H B; have hI:= strip_compose hη.le hH hB
  let V:= composeRows Y B; have hV:= strip_compose hη.le hY hB
  let E:= plusRows V D
  have hE:=strip_minus hV (strip_scale hD (-1))
  have hf : Whole E:=⟨_,_,hη,hE⟩
  let M:= composeRows R E
  have hm:= strip_compose hη.le hR hE
  refine ⟨_,strip_minus hI hm,fun c=>?_⟩
  intro S
  have he : E.acts c=V.acts c+D.acts c := (Whole.acts_plus (show Whole V from ⟨_,_,hη,hV⟩) ⟨_,_,hη,hD⟩ _)
  have hx : V.acts c=Y.acts c*B.acts c:= acts_compose hη.le hY hB c
  have hh : I.acts c=H.acts c*B.acts c:= acts_compose hη.le hH hB c
  have hg : B.acts c=repackM (unitSplit G S 1) (clothe G S) (butt G c _) := cut_delivery (G:=G) S
  have hz : M.acts c= R.acts c * E.acts c := (show Whole R from ⟨_,_,hη,hR⟩).acts hf c
  calc
    _ = I.acts c - M.acts c := acts_minus hη.le hI hm c
    _ = _ := by
      rw [hh,hz,he,hx,hg, show R.acts c=_ from father_serves (G:=G) P K c,show Y.acts c=_ from decorated_service (G:=G) S,show D.acts c=_ from covers_service (G:=G) S,show H.acts c=_ from hikes_become (G:=G) P K T c]
      let f:=c*P.L; let Z:= patron G (apices S); let x:=unitSplit G S 0; let y:=unitSplit G S 1
      let g:=butt G c f; let ψ:= patron G (fixRoot S); let l:=patron G (trails S T.forest)
      let w:= brim G c f; let d:= clothe G S; let s:= Equiv.refl (Lines G c 0)
      change _ = repackM x d (l*g-Z*(ψ*g+w))
      rw [show repackM x d (l*g-Z*(ψ*g+w))=repackM x d (l*g)-repackM x d (Z*(ψ*g+w)) from rfl,repack_multiply _ y, repack_multiply _ s, show repackM s d (ψ*g+w)=repackM s d (ψ*g)+repackM s d w from rfl, repack_multiply _ y]; rfl
lemma step_staged (G : Gauge) (P : Patch) (η : ℝ) (hη : 0<η) : ∃ C,(stepRow G P).strip η C ∧ ∀ K : KernelChoices, ∀ c : Side,
    let S:=primary P K c; (stepRow G P).acts c=repackM (unitSplit G S 1) (unitSplit G S 0) (patron G (d 0 (c*P.L))) := by
  obtain ⟨C,hC,h⟩ := delta_budget 0 η
  have hv := shades_pay (G:=G) _ hC.le h
  refine ⟨_, onBlocks_pay _ _ hη.le hv _,fun K c=>?_⟩
  intro S
  rw [show (stepRow G P).acts c=_ from (onBlocks_service _ _ S.ratio hη.le hv), shades_acts _ (cobound_safe _)]; rfl

lemma march_staged (G : Gauge) (T : Lodge P) (K : KernelChoices) (η : ℝ) (hη : 0<η) : ∃ C,
    (marchRow G P K T).strip η C ∧ ∀ c : Side,
      let S:= primary P K c; (marchRow G P K T).acts c=repackM (unitSplit G S 1) (clothe G S) (imprint G S T.forest) := by
  obtain ⟨C,hc,h⟩:=foot_staged G T K _ hη
  obtain ⟨D,hd,H⟩:=step_staged G P _ hη
  let A:= stepRow G P; let B:=footRow G P K T
  let M:= composeRows A B; let U:=cutRow G P.L
  have hb:=cut_pay G P.L η
  have he:=strip_compose hη.le hd hc
  refine ⟨_,strip_minus hb (strip_scale he (-1)),fun c=>?_⟩
  intro S
  calc
    _ = U.acts c+M.acts c := Whole.acts_plus (show Whole U from ⟨_,_,hη,hb⟩) ⟨_,_,hη,he⟩ c
    _ = _ := by
      rw [show M.acts c=_ from (acts_compose hη.le hd hc c),H K c,h c,show U.acts c=_ from (cut_delivery (G:=G) S)]
      let W:=patron G (d 0 (c*P.L)); let V:=lead G S T.forest
      rw [show imprint G S T.forest = butt G c (c*P.L)+W*V from rfl, show repackM (unitSplit G S 1) (clothe G S) (butt G c (c*P.L)+W*V) = repackM (unitSplit G S 1) (clothe G S) (butt G c (c*P.L))+repackM (unitSplit G S 1) (clothe G S) (W*V) from rfl,repack_multiply _ (unitSplit G S 0)]; rfl

set_option maxHeartbeats 450000 in
lemma close_staged (G : Gauge) (T : Lodge P) (K : KernelChoices) (η : ℝ) (hη : 0<η) : ∃ C : ℝ, 0<C ∧
    (closeRow G P K T).strip η C ∧ ∀ c : Side,
      let S:=primary P K c; (closeRow G P K T).acts c=repackM (splitting (G:=G) (S:=S) T) (clothe G S) (hang G S T.forest) := by
  obtain ⟨C,hc,h⟩:= march_staged G T K _ hη
  have hg : (touchRow T G).strip η 1:= fun _ _ => strip_unit _ _
  have hu := strip_compose hη.le hg hc
  refine ⟨_,lt_max_of_lt_left one_pos,strip_mono hu le_rfl (le_max_right ..),fun c=>?_⟩
  intro S
  rw [show (closeRow G P K T).acts c=(touchRow T G).acts c*(marchRow G P K T).acts c from acts_compose hη.le hg hc c, h c, show (touchRow T G).acts c=_ from (touch_service (G:=G) S T)]
  exact (repack_multiply (T.splitting (S:=S) (G:=G)) (unitSplit G S 1) (clothe G S) (dropRoot G S T.forest) (imprint G S T.forest)).symm
end Lodge
end YM.FormalBulk08.Flat
