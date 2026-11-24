import YM.Integration.WilsonPositionProgramPublicWide

/-! The same reflected test on both sides, including its physical dilation,
the four mixed Wilson measurements, and all original cutoff-dependent axes. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicWideHearing
open Filter Function Extraction Table Spec PhysMS Lattice Source Labels Maxwell MS MS.Menus
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus Table.Pairing Local.Physical
open WilsonThermometerUnitFilingFourSquare WilsonPositionProgramPublicContrast
open WilsonPositionProgramPublicFourPrice WilsonPositionProgramPublicWide
open WilsonPositionProgramPublicWickGram WilsonPositionProgramPublicReflectedRead
open scoped Topology BigOperators Classical
variable {G:Gauge} {B:Deck G} {h:ℕ} {K:Type} [Fintype K] (leg:K→Glyph B h)
variable {I:Type} [Fintype I] {C:Family G} {S:Table C.book} {f:Extraction.Order}
    {l:Filter (ℕ×ℕ)} [l.NeBot] {d:ℕ} (F:Final C f S)
    {m:I→S.Field d} (arm:(i:I)→Bool→Arm C S l d (m i))
    (W:Initialize G) (V:Normalize.Store G) (axis:Axis)

def profile (b:Bulb (center axis) axis) (i j:I) : Test 2 :=
  withOther (b.tests (L:=C.book) (fun _=>⟨d,(arm i false).label⟩))
    (b.tests (L:=C.book) (fun _=>⟨d,(arm j false).label⟩))

omit [Fintype I] [l.NeBot] in
theorem read (b:Bulb (center axis) axis) (i j:I) (x y:Points 1) :
    profile arm axis b i j (closedUp axis x y) = (WilsonPositionProgramPublicBulb.weight axis b (x,y):ℂ) := by
  change star (b.f (earlier axis (closedUp axis x y))) * b.f (after (closedUp axis x y))=_
  have hn: (pairIso axis) (closedUp axis x y)=(x,y) := (pairIso axis).apply_symm_apply _
  rw [equals] at hn
  have hx := congrArg Prod.fst hn
  have hy := congrArg Prod.snd hn
  change earlier axis (closedUp axis x y) = x at hx
  change after (closedUp axis x y) = y at hy
  simp [hx,hy,Bulb.f,WilsonPositionProgramPublicBulb.weight]

def paid (b:Bulb (center axis) axis) {t:ℝ} (ht:0<t) (w:I→ℂ) (z:ℕ×ℕ) (a c:Bool) : ℂ :=
  heard F (Signed.mirror axis) arm (fun i j=>Next.UVStress.dilate ht (profile arm axis b i j)) w z a c

theorem original (each:Injective leg) (order:l≤f.fuse) :
    ∃ (b:Bulb (center axis) axis) (k δ:ℝ), 0<k ∧ 0<δ ∧
      ∀ᶠ M in Front, ∀c∈M.Box, ∀ (t r:ℝ) (ht:0<t), 0<r → r≤t →
        ∀ (w:ℕ×ℕ→I→ℂ) (u:ℕ×ℕ→Bool→K→ℂ) (p:ℕ×ℕ→K→K→ℂ) (A e:ℝ),
          (∀ᶠ z in l,charge (w z)≤A) →
          (∀ᶠ z in l,‖p z-WilsonPositionProgramPublicBulb.Gram axis W V leg b M c‖≤δ) →
          (∀ᶠ z in l,∀a t',‖assay (weighted leg (r/t) (u z a)) (weighted leg (r/t) (u z t')) (p z)-
            paid F arm axis b ht (w z) z a t'‖≤e) →
          ∀η:ℝ, 0<η → ∀ᶠ z in l, k*((r/t)^h*‖u z false-u z true‖)^2≤4*e+η := by
  obtain ⟨b,k,δ,hk,hδ,margin⟩:=WilsonPositionProgramPublicBulb.original axis W V leg each
  refine ⟨b,k,δ,hk,hδ,?_⟩
  filter_upwards [margin] with M prices c hc t r ht hr hrt w u p A e mass mesh four η hη
  let test (i j:I):=Next.UVStress.dilate ht (profile arm axis b i j)
  have disappears : Tendsto (fun z=>difference (paid F arm axis b ht (w z) z)) l (𝓝 0) := by
    have signed:=WilsonPositionProgramPublicContrast.original F (Signed.mirror axis) arm arm test order
      w w mass mass
    convert signed using 2 with z
    unfold difference paid heard
    simp only [←WilsonPositionProgramPublicQuadratic.subtracted]
    rfl
  filter_upwards [mesh,four,(disappears.norm.eventually (gt_mem_nhds
    (show ‖(0:ℂ)‖<η by simpa using hη)))] with z bound fees small
  have scale := lower leg (r/t) (div_nonneg hr.le ht.le) ((div_le_one ht).mpr hrt) (u z false-u z true)
  have nonnegative : 0 ≤ (r/t)^h * ‖u z false-u z true‖ := by positivity
  have hl:=prices c hc (p z) bound (weighted leg (r/t) (u z false-u z true))
  have extended := (mul_le_mul_of_nonneg_left ((sq_le_sq₀ nonnegative (norm_nonneg _)).mpr scale) hk.le).trans hl
  rw [WilsonPositionProgramPublicWide.sub] at extended
  have combine:=common (fun a=>weighted leg (r/t) (u z a)) (fun a=>weighted leg (r/t) (u z a)) (p z)
  rw [combine] at extended
  have pay:=invoice (paid F arm axis b ht (w z) z)
    (fun a v=>assay (weighted leg (r/t) (u z a)) (weighted leg (r/t) (u z v)) (p z)) fees
  exact (extended.trans pay).trans (by linarith)
end YM.Integration.WilsonPositionProgramPublicWideHearing
