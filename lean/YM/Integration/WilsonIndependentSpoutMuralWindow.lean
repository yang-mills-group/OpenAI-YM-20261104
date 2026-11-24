import YM.Integration.WilsonIndependentSpoutOrdinaryPrimitives

/-! Footprints, ordinary unfolding and retained scalar of the Wilson top. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutMuralWindow
open Filter Function Lattice RG WilsonCoeffUV WilsonCoeffUV.Bank RegulatorIR
open RegulatorIR.Binding RegulatorIR.Geometry RegulatorIR.Geometry.Field RegulatorIR.Prim
open RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Diagram RegulatorIR.Diagram.Formal
open RegulatorIR.Ledger RegulatorIR.Oracle RegulatorIR.Calibration RegulatorIR.Ward RegulatorIR.Clocks
open WilsonIndependentSpoutFiniteStencil (Raw coordinates)
open WilsonIndependentSpoutOrdinaryPlate (base)
open scoped Classical BigOperators Topology
variable {G:Gauge}

theorem shifted (a p:Cover)(w:Walk):steps (a+p) w=rangeE a (steps p w):=by
  induction w generalizing p with
  | nil=>simp [steps,rangeE]
  | cons d w ih=>
    rw [steps,steps,rangeE,Finset.image_insert,add_assoc,ih]
    congr 1
    unfold Step.used Geometry.dis
    split <;>simp [*]
    abel

def allot : Finset (Edge Cover):=Finset.univ.biUnion fun k:PlaqAxes=>steps 0 (square k.val.1 k.val.2)
@[irreducible] def fronts (y:Foot G): Finset (Face ℤ):=(allot.image (fun d=>y.1.1-d.1)) ×ˢ Finset.univ

theorem radius {p:Face ℤ}{y:Foot G}(atArm:y∈basin G p):
    ∃d∈allot,y.1=dis p.1 d:=by
  have h:= (Finset.mem_product.mp atArm).1
  rw [show p.1=p.1+0 from (add_zero _).symm,shifted] at h
  obtain ⟨d,hd,hz⟩:=Finset.mem_image.mp h
  exact ⟨d,Finset.mem_biUnion.mpr ⟨p.2,Finset.mem_univ _,hd⟩,hz.symm⟩

private theorem offset_front (p:Face ℤ)(y:Foot G)(d:Edge Cover)(hd:d∈allot)(h:y.1.1=p.1+d.1):
    p∈fronts (G:=G) y:=by
  unfold fronts
  rw [Finset.mem_product]
  refine ⟨Finset.mem_image.mpr ⟨d,hd,?_⟩,Finset.mem_univ _⟩
  change y.1.1-d.1=p.1
  rw [h]
  abel

theorem front {p:Face ℤ}{y:Foot G}(atArm:y∈basin G p):p∈fronts (G:=G) y:=by
  have h:∃d:Edge Cover,d∈allot ∧ y.1=dis p.1 d:=@radius G p y atArm
  obtain ⟨d,hd,eq⟩:=h
  exact @offset_front G p y d hd (congr_arg (fun v:Edge Cover=>v.1) eq)

theorem originated (y:Foot G):∀ᶠ n:Side in atTop,∀p:Face (Per n),∀x:Foot G,
    x∈basin G (base p)→coordinates n x=coordinates n y→x=y:=by
  have paid (d:Edge Cover):∀ᶠ n:Side in atTop,∀b:Site n,
      wrap n (lift b+d.1)=wrap n y.1.1→lift b+d.1=y.1.1:=by
    filter_upwards [lift_ready (y.1.1-d.1)] with n hn
    intro b hb
    have atRoot:b+wrap n d.1=wrap n y.1.1:=by simpa only [map_add,wrap_lift] using hb
    have home:b=wrap n (y.1.1-d.1):=by rw [map_sub];exact eq_sub_iff_add_eq.mpr atRoot
    rw [home,hn]
    abel
  filter_upwards [(eventually_all_finset allot).mpr (fun d _=>paid d)] with n room
  intro p x arm same
  obtain ⟨d,hd,eq⟩:=radius (G:=G) (p:=base p) (y:=x) arm
  have hx:x.1.1=lift p.1+d.1:=congr_arg Prod.fst eq
  have hw:wrap n x.1.1=wrap n y.1.1:=congr_arg (fun z:Raw G n=>z.1.1) same
  have hxy:x.1.1=y.1.1:=hx.trans (room d hd p.1 (hx ▸ hw))
  exact Prod.ext (Prod.ext hxy (congr_arg (fun z:Raw G n=>z.1.2) same))
    (congr_arg (fun z:Raw G n=>z.2) same)

variable {I:Type}{M:I→ℕ}(t:Page M→Scale)(w:I)

theorem selected (p:Face ℤ)(e r:ℕ)(x:Tuple (Foot G) r)(j:Fin r)(out:x j∉basin G p):
    Circuit.mural G t w p e r x=0:=by
  let E:=basin G p
  apply WilsonIndependentSpoutLocalSupport.pixels (placeFin E) (Circuit.serene G t w p) _ e r x j
  · rintro ⟨z,h⟩;exact out (h ▸ z.property)
  intro v X Y h
  apply congr_arg (fun k:G.El=>(t (Page.opening M w)).beta v*G.price k)
  apply travel_knows;intro i hi
  apply congr_arg G.lieExp
  ext1 j
  exact congr_fun h (⟨(i,j),Finset.mem_product.mpr ⟨hi,Finset.mem_univ _⟩⟩:↥E)

theorem scalar (p:Face ℤ)(e:ℕ):Circuit.mural G t w p e 0=0:=
  (Circuit.serene G t w p).no_altar (plain_rest (t (Page.opening M w)) G p) e

end YM.Integration.WilsonIndependentSpoutMuralWindow
