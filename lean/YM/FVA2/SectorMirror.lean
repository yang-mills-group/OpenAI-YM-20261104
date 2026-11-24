import YM.FVA2.Halves
/-!
# Orientation of fields. Link-Haar and pinned tests will see this same lift
 at every frontier. Parameter.Page.D.Edge.Free mirrors preserving branch exact.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.Both
open Function Filter Topology MeasureTheory Lattice Gauge RG _root_.YM.Wilson
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10 FormalOPE.RG10.Inherit FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice FormalOPE.RG10.BlockGauge
open PertExtension.Orb Precision GaussianScore RGComparison.Core16 RGComparison.Core16.Descent Tree Exterior Push.BetaTransport Tandem Luggage
open MeasureTheory.Measure (IsAddHaarMeasure)
open Contacts.Lyre Contacts.Lyre.Align Fabric CityHistory Mirror
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c f n:Side}
local notation "V"=> Pins G n
local notation "Q"=> Flats G n

-- full reflections.Gl.Link

noncomputable def ref (G:Gauge) (n:Side) : Pins G n→ₗ[ℝ] Pins G n:= LinearMap.pi fun i=> -(LinearMap.proj (Orb.reflect i))
lemma red (p: Pins G n)(i:Edge (Site n)): (ref G n p) i = -p (Orb.reflect i):= rfl
lemma ref_house (e : V) : ref G n (ref G n e)=e:= funext (fun i=>by rw [red,red, reflect_reflect, neg_neg])
abbrev flare (G:Gauge)(n:Side): Pins G n→ₗ[ℝ] Flats G n:= LinearMap.pi fun i=> LinearMap.proj i.val

def orb (G: Gauge)(n:Side)(he: Even n.val): Mirror.House (Pins G n) (Flats G n):={
   t:=ref G n
   inv:= ref_house
   ε:= Trans.coverL G n
   assess:= fun x=> funext (fun i=> by rw [red, Trans.cover_reflect G n he, neg_neg])
   π:= flare G n
   lift:= fun x hx=> Trans.own_image G n (fun i=>Eq.symm (congr_arg Neg.neg ( Eq.symm (congr_fun hx i) ) |>.trans (neg_neg _)))
   recovery:= fun y=> funext (Trans.coverL_at G n y) }

lemma lamps (p : Pins G n) : expLinks G _ (ref G n p)= Lattice.pull Align.inverse 0 (expLinks G _ p):= by ext1 i; rw [ flip_channel, expLinks, red, Next.SectorChange.exp_negative ]; rfl -- orientation 👣

-- only projected compatible homotopies.Please support clocks.St.
variable (S:StepData c f)
local notation "T" => Forestry S
local notation "P" => canopy S
local notation "M" => Blocking.Cross (G:=G) S P
local notation "A" => Future G S ( Forestry S )
local notation "r"=> ref G f
open Blocking

def atRef (G:Gauge)(S:StepData c f): Future G S ( Forestry S )→ₗ[ℝ] Future G S (Forestry S):= LinearMap.pi fun i=> -(LinearMap.proj ( Align.via S i ))

lemma sub_ref (x:A)(i:(T).Free) : atRef G S x i= -x ( Align.via S i ):= rfl
lemma full_reflect (u:A) : ref G f ( pext G S T u )= pext G S T (atRef G S u):= by
     ext1 i; rw [red]; by_cases h:i ∈ (T).trunks
     · simp [ pext,trunk,h ]
     rw [ pext ]; simp only [ LinearMap.pi_apply, dif_neg h, dif_neg (mt (Align.trunk S i).mp h), LinearMap.proj_apply ]; rfl

-- compare indices with exact projection to representative chosen by MS.Org.

def rootFree (i: Blocking.Index S P): (T).Free := ⟨ i.val.val,(branch_ident S i.val).not.mp i.property ⟩
def upF (i : (T).Free)(h:eR i.val=i.val) : Blocking.Index S P:= ⟨ ⟨i.val,h⟩,(branch_ident S (⟨i.val,h⟩:OEdge f)).not.mpr i.property ⟩

def takeF (G:Gauge)(S:StepData c f): Future G S ( Forestry S )→ₗ[ℝ] Blocking.Cross (G:=G) S (canopy S):= LinearMap.pi fun i=> LinearMap.proj (rootFree S i)
abbrev litF (G:Gauge)(S:StepData c f): Blocking.Cross (G:=G) S (canopy S) →ₗ[ℝ] Future G S ( Forestry S ):= LinearMap.pi (fun ( i : (Forestry S).Free ) => LinearMap.proj i.val ∘ₗ Trans.coverL G f ∘ₗ OpenSlots.extend (canopy S))
abbrev extG (x:M):= Trans.coverL G f (OpenSlots.extend P x)
lemma signal (x: M) : pext G S T (litF G S x)=Trans.coverL G f ( OpenSlots.extend P x ):= by
     funext i; by_cases h:i∈ (T).trunks
     · rw [pext, LinearMap.pi_apply, dif_pos h ]; have he: ( Orb.index i ).val∈ (T).trunks := (branch_copied S i).mpr h; have hm: Inside.Innate (P) ( Orb.index i ):= ( branch_ident S ( Orb.index i ) ).mpr he; have hu : OpenSlots.extend P x (Orb.index i)=0:= by rw [OpenSlots.extend, LinearMap.pi_apply,dif_pos hm]; rfl
       unfold Trans.coverL; simp only [LinearMap.pi_apply]; split; exact hu.symm; change 0= - OpenSlots.extend P x _; rw [hu,neg_zero]
     rw [pext, LinearMap.pi_apply,dif_neg h,LinearMap.proj_apply ]; rfl
lemma refunds (x: M) : takeF G S (litF G S x)=x:= by
     funext i; change Trans.coverL G f ( OpenSlots.extend P x ) i.val.val=_; rw [ Trans.coverL_at ]; unfold OpenSlots.extend; rw [ LinearMap.pi_apply, dif_neg i.property ]; rfl
lemma startup (x:A)(i:(T).Free): pext G S T x i.val=x i:= by rw [pext,LinearMap.pi_apply,dif_neg i.property]; rfl
lemma pext_inj : Injective (pext G S ( Forestry S )):= fun x y h=> funext (fun i=>Eq.trans (startup S x i).symm (( congr_fun h i.val ).trans ( startup S y i )))

variable (hf:Even f.val)
local notation "Hf"=> orb G f hf
local notation "Lp"=> (Hf).ε
include hf
lemma wind (x:A)(h:atRef G S x=x): Trans.coverL G f (OpenSlots.extend P (takeF G S x))= pext G S T x:= by
     have he : (Hf).t (pext G S T x)=pext G S T x:= by change ref G f _=_; rw [ Both.full_reflect,h ]
     suffices ht: OpenSlots.extend P (takeF G S x)= (Hf).π (pext G S T x) from ht ▸ (Hf).lift _ he
     funext i; by_cases h:i.val∈ (T).trunks
     · change _=pext G S T x i.val; rw [ OpenSlots.extend,LinearMap.pi_apply,dif_pos ((branch_ident S i).2 h), pext,LinearMap.pi_apply,dif_pos h ]; rfl
     change _=pext G S T x i.val; rw [OpenSlots.extend,LinearMap.pi_apply,dif_neg ((branch_ident S i).not.mpr h), pext,LinearMap.pi_apply,dif_neg h ]; rfl

def lights (G:Gauge)(S:StepData c f)(hf:Even f.val): Mirror.House (Future G S (Forestry S)) (Blocking.Cross (G:=G) S (canopy S)):={
    t:=atRef G S
    ε:= litF G S
    π:= takeF G S
    inv:= fun x=> funext (fun i=> by rw [sub_ref,sub_ref, via_via, neg_neg])
    lift:= fun x h=> pext_inj S (Eq.trans (signal S ( takeF G S x)) (wind S hf x h))
    assess:= fun x=> pext_inj S (Eq.trans (Both.full_reflect S _).symm (Eq.trans (congr_arg (ref G f) (signal S x)) (Eq.trans ((Both.orb G f hf).assess _) (signal S x).symm )))
    recovery:= refunds S }
local notation "Le"=> (lights G S hf)
lemma gate_ε (Z : Flats G c)(X:M)(hc:Even c.val) : gate G S ( Forestry S ) ( ( (lights G S hf).join (Both.orb G c hc) ).ε ( X,Z ) ) = Trans.coverL G f ( blankRight (canopy S) ( X,Z ) ):= signal S _
-- proof explicit price chapters ahead.Trajectory.Pulse.Depth tick. Handle both appended and root.
end YM.FVA2.Both
