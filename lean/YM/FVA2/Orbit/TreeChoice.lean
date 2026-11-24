import YM.FVA2.Orbit.Trees
/-!
# Permitted tree from the published rooted alignment
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Orbit.Grove
open Function Set Filter Finset Topology Lattice PertExtension PertExtension.Orb LocalH
open scoped ContDiff Topology Matrix.Norms.Frobenius Classical BigOperators
variable {G:Gauge} {n:Side} (ev: Even n.val)
local notation "I" => OEdge n
local notation "S" => Branch (n:=n)
local notation "V" => Rep G n
local notation "H" => Direct G S
local notation "W" => Complement G S
local notation "F" => Pert.Orb.Potential G n
local notation "R" => Root G n
local notation "Z" => Pert.Orb.Parameter G n
local notation "C" => G.Color
lemma risen (x:W)(i:I) : rise S x i= genJet x i:= by unfold rise genJet; rw [LinearMap.pi_apply]; split <;> rfl
lemma tree_ignite (p:W) : ignite (rise S p) = representative p:= by
    unfold ignite representative links; congr 1; funext i; unfold splitLink; rw [comp_apply,risen]; by_cases h:Branch i <;> simp [h,genJet]
include ev
lemma tree_lift (x:W) : (fan ev (rise S x)).val=variation x:= by
    let p:=fan ev (rise S x); have h (i:I) : p.val i.val=genJet x i:= by rw [← risen,← read_fan ev (rise S x)]; rfl
    have he (i:I): p.val i.val=variation x i.val:= by rw [h,variation_at]
    exact congr_arg (fun p:F=>p.val) (rep_inj (G:=G) (n:=n) (a₁:=p) (a₂:=(⟨variation x,variation_invert ev x⟩:F)) (funext he))
private theorem inj : Injective (take S ∘ₗ vertical (0:V)):= by
  apply LinearMap.ker_eq_bot.mp; apply bot_unique; intro x hx
  change take S (vertical 0 x)=0 at hx; rw [vertical_flat,map_neg,neg_eq_zero] at hx
  let z := Pert.Orb.gZ (gaugeAngles G n x); let a:= leave S (touches G n z); have hh:rise S a= touches G n z:= joint _ ((rise_nil S a).trans hx.symm) (rise_up S a)
  have hk : fan ev (rise S a)=z:= rep_inj ((read_fan ev (rise S a)).trans hh)
  let f:= fun t:Lattice.Site n=>atSite t x; have hm (i:Lattice.Edge (Lattice.Site n)) : variation a i=f i.1-f (i.1+step i.2):= by rw [←tree_lift ev,hk]; rfl
  have hq : a=0:= curl_gap ev a (by intro t i j; rw [Curl]; simp only [hm, add_right_comm t]; abel)
  have ho : z=0:=rep_inj (a₁:=z) (a₂:=(0:F)) (show touches G n z=_ from by rw [←hh,hq]; simp)
  have ht : gaugeAngles G n x=0:= Pert.Orb.bridge_inj (show Pert.Orb.dLin z= (Pert.Orb.bridge G n) 0 from by rw [map_zero,ho,map_zero])
  exact (gaugeAngles G n).injective (ht.trans (map_zero _).symm)
private theorem onto : Surjective (take S ∘ₗ vertical (0:V)):= by
    -- For any assigned tree logs, frame in the additive color group gives an inverse gradient.
    intro y; let K':= Multiplicative C; let b (i:Trees n):K':= Multiplicative.ofAdd (y i); let p:=frame b
    have he:p 0=1:= by rw [show p 0=frame b 0 from rfl,frame]; simp
    let z : Z:= ⟨fun x=> Multiplicative.toAdd (p x), ⟨fun x=> congr_arg Multiplicative.toAdd (frame_neg _ x), show (Multiplicative.toAdd (p 0))=0 from congr_arg (fun v=> Multiplicative.toAdd v) he⟩⟩
    refine ⟨(gaugeAngles G n).symm z,?_⟩; rw [LinearMap.comp_apply,vertical_flat,map_neg,LinearEquiv.apply_symm_apply]; funext i; have h:= tree_zero ev b (fun _=>1) i; unfold aligned Lattice.gauge at h; rw [links,lift_at, splitLink,dif_pos i.property] at h
    have hh:= congr_arg Multiplicative.toAdd h; let x:= i.val.val; change - (z.val x.1 - z.val (x.1+step x.2))= y i; change z.val x.1 + y i + (-(z.val (x.1+step x.2)))=0 at hh; rw [show -(z.val x.1-z.val (x.1+_))= y i - (z.val x.1+y i+(-(z.val (x.1+step x.2)))) from by abel,hh,sub_zero]
theorem permitted : Permitted G S:= ⟨inj ev,onto ev⟩
def rooted (G:Gauge) {n:Side} (ev:Even n.val): Screen G n (Orb.Dir G n):= shrub G Branch (permitted ev)
-- analytic general argument via gauge change
end YM.FVA2.Orbit.Grove
