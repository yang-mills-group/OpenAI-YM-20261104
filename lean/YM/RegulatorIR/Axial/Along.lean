import YM.RegulatorIR.Gain.Orbits
import YM.RegulatorIR.Axial.Deeper

/-!
# θ-free limit of axial sheets
Figures as before, prices only at each *fixed* release. Rotate sheet center
independently so no symmetry constraint on kernels. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Axial
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight PowerSeries Gain Prim Motion Budget.Packet
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries
variable {G:Gauge} {s m p k:ℕ}
variable (p:Signed) (f:Side)
section Geo
variable (z:Side)

abbrev spark (p:Signed)(z:Side):Motion:=Motion.across (p.act (journey z))
def centreE := f.val • p.act (journey z)
def shifting := dis (centreE p f z)
def entering (x:Cover):= wrap (rep f z) (centreE p f z+x)
def secure (x:Edge Cover):Edge (Site (rep f z)):=(entering p f z x.1,x.2)
lemma secure_eq : secure p f z=around (rep f z) ∘ shifting p f z:=rfl
def sig (x: Edge Cover):OEdge (rep f z):=index (secure p f z x)
lemma centre_at : centreE p f z=p.act (fromZ f z):=Eq.symm (map_nsmul (p.actEquiv (R:=ℤ)) _ _)
lemma pulled_in (x: Cover) : entering p f z (p.act x)=p.act (swim f z x):=by unfold entering;rw [centre_at,←p.act_add,← wrap_signed];rfl -- sign

def rotateE (p:Signed)(x: Edge Cover):Edge Cover:= ((posDir x.2).rotate p).used (affine p 0 x.1)
lemma brought (x:Edge Cover)(s:Side) : around s (rotateE p x)=sent p (around s x):=by
 unfold rotateE sent sendEdge affine; rw [add_zero,add_zero]
 let d:= (posDir x.2).rotate p
 change around s (d.used _) = d.used _; unfold around Step.used; split <;> dsimp only <;> first| (rw [map_sub,wrap_step,← wrap_signed]) | (rw [← wrap_signed])
lemma shield (x:Edge Cover): shifting p f z (rotateE p x)=rotateE p (deep f z x):=by
 let d:= (posDir x.2).rotate p;change dis _ (d.used _) = d.used (p.act (fromZ f z+_)+0); rw [p.act_add,centre_at]
 unfold affine dis Step.used;split <;> dsimp only <;> first| (rw [add_zero,add_zero,add_sub_assoc]) | (rw [add_zero,add_zero])
lemma secured (x: Edge Cover) : secure p f z (rotateE p x)= sent p (around (rep f z) (deep f z x)):=by rw [secure_eq,comp_apply,shield,brought]
lemma entered (x:Cover)(a : Axis) : entering p f z (x+step a)= entering p f z x+step a:=by unfold entering;rw [← add_assoc,map_add,wrap_step]
-- geometrical inverse coordinates
lemma reverted (x:Edge Cover) : rotateE p⁻¹ (rotateE p x)=x:=by
 let i:=posDir x.2;let d:= i.rotate p
 have hx:d.rotate p⁻¹=i:=by rw [show d=i.rotate p from rfl, Step.rotate_mul,inv_mul_cancel, Step.rotate_one]
 let b:= p.act x.1; have hh : rotateE p x=d.used b:=by unfold rotateE affine; rw [add_zero]
 rw [hh]; unfold rotateE affine
 cases he:d.neg
 · have hp: posDir d.dir=d:=by obtain ⟨s,b⟩:= d; exact congr_arg _ he.symm
   rw [show d.used b= (b,d.dir) from by simp [Step.used,he]]
   change ((posDir d.dir).rotate p⁻¹).used _= _;rw [hp,hx]; change (p⁻¹.act (p.act _)+0,_) = _;rw [p.inv_act,add_zero]
   rfl
 have hp: posDir d.dir=d.rev:=by obtain ⟨s,q⟩:=d; dsimp [Step.rev]; rw [show q=true from he];rfl
 rw [show d.used b=(b+d.vec,d.dir) from by simp [Step.used,Step.vec,he,sub_eq_add_neg]]
 change ((posDir d.dir).rotate p⁻¹).used (p⁻¹.act (b +d.vec)+0)= _; rw [hp,Step.rev_rotate,hx,add_zero,p⁻¹.act_add,← Step.vec_rotate d p⁻¹,hx]; change (p⁻¹.act (p.act x.1)+ (step x.2)-step x.2,x.2)=_; rw [p.inv_act,add_sub_cancel_right]

def revol : Equiv.Perm (Edge Cover) where
 toFun:= rotateE p
 invFun:=rotateE p⁻¹
 left_inv:=reverted p
 right_inv x:=by simpa using reverted p⁻¹ x
lemma step_cover (e: Edge Cover) : blink p (around f e)=(e.2 |> p.flip):=by unfold blink; change false.xor _= _;simp;rfl
-- eventually independent payload. Lift.Tools equation for other centers
lemma line_route (e: Edge Cover): route p (index (around (rep f z) (deep f z e)))= sig p f z (rotateE p e):=by
 rw [sig,secured,route]; let s:=around (rep f z) (deep f z e)
 change index (sent p (eR s))= _
 rcases eR_spec s with h|h
 · rw [h]
 rw [h,sent_there]; exact Subtype.ext (eR_reflect _)
end Geo
variable {P l:ℝ}(h:Even f.val)(hp:l*f.val=P)(he:4≤f.val)
local notation "A" => Carto G l P h hp
include he
lemma fades (x y:Edge Cover): ∀ᶠ z:Side in atTop,sig p f z x=sig p f z y→ x=y:=by
 obtain ⟨i,rfl⟩:=(revol p).surjective x;obtain ⟨j,rfl⟩:=(revol p).surjective y
 filter_upwards [included i.1,included j.1] with z hx ht h
 change sig p f z (rotateE p i)=sig p f z (rotateE p j) at h;rw [←line_route,←line_route] at h
 rw [edged he hx ht ((routed p) h)]
lemma clear (x y: Foot G) : ∀ᶠ z:Side in atTop,(playS (Sight.slab z) h hp).orbit ((A).wind (spark p z) x)=(playS (Sight.slab z) h hp).orbit ((A).wind (spark p z) y) → x=y:=by
 filter_upwards [fades p f he x.1 y.1] with z hz hh
 exact Prod.ext (hz (congr_arg Prod.fst hh)) (congr_arg (fun p:Book G (rep f z)=>p.2) hh)
end YM.RegulatorIR.Axial
