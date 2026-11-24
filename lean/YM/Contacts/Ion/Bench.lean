import YM.Contacts.Ion.Held
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
open Spark
-- No minimal size nor even period assumption for spin commutation; full chart. Measured hot is exactly its mirror (observed in orbit block before gauge).
variable {f:Side}(S:StepData m f)(h:Even f.val)
abbrev SplitSpace := Rem S → G.Color
local notation "Λ"=> (SplitSpace (G:=G) S)
local notation "Θ" => (Forestry S)
local notation "Κ"=> (Precision.AxisChart G Θ)
def own (v:(Θ).Free): Rem S:= ⟨PertExtension.Orb.index v.val, fun he=> by rcases eR_spec v.val with h|h; exact v.property (h ▸ (show eR _∈ (Θ).trunks from he)); exact mt (trunk S _).mp v.property (h ▸ (show eR _ ∈ (Θ).trunks from he))⟩
def attic (v:Rem S):(Θ).Free:= ⟨v.val.val,v.property⟩
lemma purple (v:Rem S): own S (attic S v)= v:=Subtype.ext (Subtype.ext v.val.property)
def via (v: (Θ).Free): (Θ).Free:= ⟨reflect v.val,mt (trunk S _).mp v.property⟩
lemma via_via : Involutive (via S):= fun _ => Subtype.ext (reflect_reflect _)
lemma via_own (v:(Θ).Free) : own S (via S v)= own S v:= Subtype.ext (Subtype.ext (eR_reflect _))
lemma bloom (v:(Θ).Free): v=attic S (own S v)∨ v=via S (attic S (own S v)):= (eR_spec v.val).elim (fun h=> Or.inl (Subtype.ext h.symm)) (fun h=> Or.inr (Subtype.ext (Eq.symm ((congr_arg reflect h).trans (reflect_reflect _)))))
def shineDance : Λ →L[ℝ] Κ := ContinuousLinearMap.pi fun j=> if eR j.val=j.val then ContinuousLinearMap.proj (own S j) else -(ContinuousLinearMap.proj (own S j))
local notation "L" => shineDance S
local notation "Xη"=> Active G Θ
local notation "E"=> tribe S Θ
lemma spot (v:Λ)(i:Rem S): (L v (attic S i))= v i:= by rw [shineDance,ContinuousLinearMap.pi_apply,if_pos (show eR (attic S i).val=(attic S i).val from i.val.property),purple]; rfl
lemma spot_pay (v:Λ):‖v‖≤‖L v‖:= (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (fun i=> spot S v i ▸ norm_le_pi_norm (L v) (attic S i))
local notation "Ξ" => orderTurn Align.inverse
local notation "Σv"=> stash S Θ
lemma transit (y:Κ): Ξ (Σv y)= Σv ((E).symm (spin_active (E y))):= by
   change Ξ (_*ᵥ E y)= insertion (plant (G:=G) Θ) *ᵥ (E ((E).symm _)); rw [(E).apply_symm_apply, plunge] -- precedence
include h
lemma spot_neg (v:Λ)(i:Rem S): (L v (via S (attic S i)))= -v i:= by rw [shineDance,ContinuousLinearMap.pi_apply, via_own,purple, if_neg (?_)]; rfl; exact fun he=> no_fixed_edge h i.val.val ((i.val.property.symm.trans (eR_reflect i.val.val).symm).trans he).symm
lemma dance (v:Λ) (i:(Θ).Free): L v (via S i)= -(L v i):= by
   obtain ⟨j,hj⟩:∃ j:Rem S,i=attic S j∨i=via S (attic S j):=⟨own S i,bloom S i⟩; rcases hj with rfl|rfl; rw [spot,spot_neg S h]; rw [via_via,spot,spot_neg S h,neg_neg]
lemma illuminate (v:Λ) : spin_active (E (L v))= E (L v):= by funext i; unfold spin_active; rw [show E (L v) (pall i)= (L v (via S i.1)) i.2 from rfl,dance S h]; change -(-(E (L v) i))= _; rw [neg_neg]
lemma supply (x:House.Dir Xη)(hx: spin_active x=x): let v:Λ:= fun i=> (E).symm x (attic S i); L v= (E).symm x:= by
   intro v; let Q:=(E).symm x; ext1 i; obtain ⟨j,hj⟩:∃ j:Rem S,i=attic S j∨i=via S (attic S j):=⟨own S i,bloom S i⟩; rcases hj with rfl|rfl; exact spot S v j; rw [spot_neg S h]; ext1 k; let o:= attic S j; change -x (o,k) = x (via S o,k); have he: pall (via S o,k)= (o,k):= Prod.ext (via_via ..) rfl; rw [show x (o,k)=_ from (congr_arg x he.symm)]; exact congr_fun hx (via S o,k) -- instances
lemma sight (v:Λ): Ξ (Σv (L v))= Σv (L v):= by rw [transit,illuminate S h,(E).symm_apply_apply]
end Align
end
end YM.Contacts.Lyre
