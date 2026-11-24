import YM.Integration.WilsonIndependentSpoutLocalSupport

/-! The finite support here is the actual emitted Haar edge or the declared
lower edge together with the complete prediction stencil of its spring. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutPrimitiveWindow
open Lattice RG RegulatorIR RegulatorIR.Binding RegulatorIR.Geometry RegulatorIR.Geometry.Field
open RegulatorIR.Prim RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Diagram RegulatorIR.Diagram.Formal
open RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Halo Tree
open scoped Classical BigOperators
variable {G:Gauge}{c n:Side}

def sites (G:Gauge)(P:Patch):Branchix→Finset (KFoot G)
  | .inl a=>Finset.univ.image fun j:G.ColorIndex=>Sum.inl ((a,j):Foot G)
  | .inr a=>((lantern P a×ˢFinset.univ).image (Sum.inl:Foot G→KFoot G))∪
      Finset.univ.image (fun j:G.ColorIndex=> Sum.inr ((a,j):Foot G))

theorem native (S:StepData c n)(F:Forest S.ratio)(branch:S.patch.Branches S.kernel G)
    (K:Scale){T:Branchix→Orders (KFoot G)}(book:Sphere S F K T)
    (b:Branchix)(e r:ℕ)(w:Tuple (KFoot G) r)(j:Fin r)(outside:w j∉sites G S.patch b):
    T b e r w=0:=by
  let E:=sites G S.patch b
  apply WilsonIndependentSpoutLocalSupport.pixels (placeFin E) (book b) _ e r w j
  · rintro ⟨z,hz⟩;exact outside (hz ▸ z.property)
  intro t x y agree
  have seen (z)(inside:z∈E):x z=y z:=congr_fun agree (⟨z,inside⟩:↥E)
  cases b with
  | inl a=>
    change carnal S F a t x=carnal S F a t y
    unfold carnal
    split
    · rfl
    congr 1
    ext j
    exact seen (.inl (a,j)) (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
  | inr a=>
    change opi S K a t x=opi S K a t y
    have eq:win G (x ∘ Sum.inr) a=win G (y ∘ Sum.inr) a:=by
      apply congr_arg G.lieExp
      ext j
      exact seen (.inr (a,j)) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
    have pred:pond S.patch S.kernel (win G (x ∘ Sum.inl)) a=pond S.patch S.kernel (win G (y ∘ Sum.inl)) a:=by
      apply pond_low S.patch S.kernel branch
      intro p hp
      apply congr_arg G.lieExp
      ext j
      exact seen (.inl (p,j)) (Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨(p,j),Finset.mem_product.mpr ⟨hp,Finset.mem_univ _⟩,rfl⟩))
    unfold opi
    rw [eq,pred]

theorem selected {W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}
    (C:Circuit M sides)(Z:∀P:Patch,P.Branches K G)(D:RegulatorIR.Calibration.Tent M)(f:Flap M)
    (b:Branchix)(e r:ℕ)(w:Tuple (KFoot G) r)(j:Fin r)
    (outside:w j∉sites G (C.pactP f) b):
    C.bore G Z (RegulatorIR.Calibration.sheet D) f b e r w=0:=
  native (C.rail K f) (bios (C.rail K f)) (Z _) _ (C.wheeled G Z _ f) b e r w j outside

end YM.Integration.WilsonIndependentSpoutPrimitiveWindow
