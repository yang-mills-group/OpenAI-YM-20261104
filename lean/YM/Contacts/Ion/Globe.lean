import YM.Contacts.Ion.Solid
import YM.PertExtension.OrbHaar
namespace YM.Contacts.Lyre
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie Harrier Sequent
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k i r l j M D:ℕ}{ζ σ:ℝ≥0}
open UVNext PricedKernels Next.Free Lattice Tree FreeResolvent
open PertExtension.Orb MeasureTheory
namespace Align
set_option autoImplicit false
abbrev orb (n:Side):= OEdge n
abbrev SLink (n:Side):= Edge (Site n)
abbrev Entry (G:Gauge)(n:Side):= orb n → G.El
def inverse : Signed:= ⟨Equiv.refl _,fun _=>true⟩
local notation "ιX"=> Align.inverse
lemma impl (x:Site m) : Align.inverse.act x=-x:= rfl
lemma flip_channel (U:Config G m)(x:Edge (Site m)): Lattice.pull ιX 0 U x = (U (reflect x))⁻¹:= by
   rcases x with ⟨x,i⟩; unfold Lattice.pull; change _= (U (-x - step i,i))⁻¹; unfold Step.read; change (U (-x+0-step i,i))⁻¹=_; rw [add_zero]
lemma warp (T: Patch) : T.orient ιX (T.center,1)=(T.center,1):= Prod.ext (T.at_zero ..) (by apply Equiv.ext; intro i; rfl)
variable {f:Side} (S:StepData m f)(hB:S.patch.Branches S.kernel G)
lemma strophic : S.withinChoice ιX 0 (art S)=art S:= by
   refine Prod.ext (funext fun i=>?_) (funext fun i=>?_); exact Align.warp _; exact S.patch.at_zero _
local notation "vX"=> (S.prediction · (art S))
def Halo (V:Config G m): Prop:=∀ i,V (reflect i)=(V i)⁻¹ -- n binder Nat issue
lemma unwrinkle (U:Config G m) : Halo U↔ Lattice.pull ιX 0 U=U:= ⟨fun h=> funext fun i=> (flip_channel U i).trans (by rw [h]; exact inv_inv (U i)),fun h i=> (inv_injective (G:=G.El)) ((flip_channel U i).symm.trans ((congr_fun h i).trans (inv_inv _).symm))⟩ -- name
include hB
lemma split_pure (V : Config G f) : S.prediction (Lattice.pull ιX 0 V) (art S)=Lattice.pull ιX 0 (S.prediction V (art S)):= by
    have ht:=S.prediction_channel hB ιX 0 V (art S); rw [Align.strophic,show S.ratio.embed 0=0 from map_zero S.ratio.root] at ht; exact ht
lemma glory (V:Config G f)(h:Halo V):Halo (S.prediction V (art S)):= (unwrinkle _).mpr (by rw [←split_pure S hB V, show Lattice.pull ιX 0 V=V from (unwrinkle _).1 h])
-- brand cash. all beta.
def dawn (p:Config G f)(c:Config G m)(u:SLink m):ℝ:= G.price (c u*(S.prediction p (art S) u)⁻¹)
abbrev orbitC (x:Entry G f)(c:Entry G m):ℝ:= ∑ i:orb m, dawn S (liftLinks x) (liftLinks c) i.val
lemma twice (A:Entry G f)(B:Entry G m)(hf:Even f.val)(hm:Even m.val)(x:SLink m): dawn S (liftLinks A) (liftLinks B) (reflect x)=dawn S (liftLinks A) (liftLinks B) x:= by
   let Q:= S.prediction (liftLinks A) (art S); let b:=liftLinks B x; let a:=Q x; unfold dawn; rw [lift_flip hm,glory S hB _ (lift_flip hf A) x]; change G.price (b⁻¹*(a⁻¹)⁻¹)= G.price (b*a⁻¹); rw [show b⁻¹*(a⁻¹)⁻¹=b⁻¹*(b*a⁻¹)⁻¹*b from by group]; rw [show b⁻¹*(b*a⁻¹)⁻¹*b=b⁻¹*(b*a⁻¹)⁻¹*(b⁻¹)⁻¹ from by rw [inv_inv],G.price_conj,G.price_inv]
omit hB
lemma bank_card : (fun x:orb m=>PertExtension.Orb.index x.val)=id := funext fun x=> Subtype.ext x.property
abbrev double (p:orb m × Bool): SLink m:= if p.2 then reflect p.1.val else p.1.val
lemma brand (x:orb m × Bool): PertExtension.Orb.index (double x)=x.1:= by
   unfold double; split; · exact Subtype.ext ((eR_reflect _).trans x.1.property)
   exact congr_fun bank_card _
lemma bar_slide (hm:Even m.val): Bijective (double (m:=m)):= by
   constructor
   · rintro ⟨a,p⟩ ⟨b,q⟩ h; have hh:(a:orb m)=b:= (brand (a,p)).symm.trans ((congr_arg PertExtension.Orb.index h).trans (brand _)); subst b; cases p<;> cases q <;> first| rfl |exact (no_fixed_edge hm a.val h).elim | exact (no_fixed_edge hm a.val h.symm).elim
   intro x; rcases eR_spec x with he|he; exact ⟨(PertExtension.Orb.index x,false),he⟩; refine ⟨(PertExtension.Orb.index x,true),?_⟩; change reflect (eR x)= _; rw [he,reflect_reflect]
lemma entry_total (P:SLink m→ℝ)(hm:Even m.val) (he:∀ x,P (reflect x)=P x): (∑ i,P i)=2*∑ i:orb m,P i.val:= by
    let e:= Equiv.ofBijective Align.double (bar_slide hm); rw [← Equiv.sum_comp e P, Fintype.sum_prod_type,Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=> ?_; rw [Fintype.sum_bool]; change P (reflect i.val)+ P i.val= _; rw [he,two_mul]
include hB
theorem estimate (A:Entry G f)(B:Entry G m) (hm:Even m.val)(hf:Even f.val): (∑ i:SLink m,dawn S (liftLinks A) (liftLinks B) i)=2*orbitC S A B:= entry_total _ hm (twice S hB A B hf hm)
end Align
end
end YM.Contacts.Lyre
