import YM.Contacts.Harrier.Ticket
import YM.Contacts.Prairie.Pear
namespace YM.Contacts.Harrier
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k h i r l j M D:ℕ}{ζ σ:ℝ≥0}
namespace Transfer
open Parcel Prairie Planned.PrimaryIntegral295
-- primitive exp(g) link-coordinate move at variable-step ports.LPT program
variable (e:Parcel G) (p:Word)(s:Parcel.Step)(M h:ℕ) {S:Boom} (T:e.License S ζ)(hp:OK S p)(hs:s∈S)
section
include T hp
@[simps! P Q K W X] def crafts : Theater G := ⟨e.flag s,e.K,e.column p,e.column (s::p),e.Q,e.valid,e.gas p s,e.wheel p s,e.port p,e.edge,e.awake p s,(T.prosper hp).blazing⟩
omit T hp
abbrev standard (F:bore G):= hearthC M (e.raw p s) (e.beam p s) (clan e.Q (e.flag s) e.K (e.port p)) (advection (e.flag s) F)
def freshen (F:bore G) := recoil (sink e.x (e.kickoff p s)) M (standard e p s M F)
def curb (z:Site s.L): Cover:= lift z
def foot (z: Site s.L) := ((s.L.val:ℝ)⁻¹) • Place.seat (curb s z)
def desk (z:Site s.L)(φ:Cards):= Cards.onRoute (foot s z) ((s.L.val:ℝ)⁻¹) φ
lemma desk_tick (z:Site s.L) : ‖foot s z‖+(s.L.val:ℝ)⁻¹*4≤4:= by
   let L:= s.L; have he: size (lift z)≤ 2*s.L.val:= by
      refine le_trans (b:=∑ i:Axis,s.L.val/2) ?_ ?_; · unfold size; apply Finset.sum_le_sum; intro i _; have h:= lift_centers z i; omega
      simp [Axis]; omega
   have hh:= side_pos L; have hl:3 ≤ (s.L.val:ℝ):= (by exact_mod_cast s.prod); let l:ℝ:=s.L.val; let H:=Carrier.shade_seat (lift z); unfold foot curb; rw [norm_smul, Real.norm_of_nonneg (by positivity)]; have hv: ‖Place.seat (lift z)‖ ≤ 2*l:= H.trans (by unfold l; exact_mod_cast he); change l⁻¹*_+l⁻¹*_ ≤ _; rw [← mul_add,mul_comm,← div_eq_mul_inv]; apply (div_le_iff₀ hh).2; unfold l at *; linarith only [hv,hl]
lemma desk_cost (v:Site s.L)(φ:Cards)(h:Costs D φ b)(hb:0≤b): Costs D (desk s v φ) b := Port.nest_card (desk_tick s v) φ h hb
lemma ldesk (v:Site s.L): IsLinearMap ℝ (desk s v):= ⟨fun _ _=>rfl,fun _ _=>rfl⟩
abbrev weigh (v:Site s.L)(F:Sketch G) : Sketch G:= fun φ=> standard e p s M (migrated (F (desk s v φ)) (curb s v))
abbrev pass (v:Site s.L)(F:Sketch G) : Sketch G:= fun φ=> recoil (sink e.x (e.kickoff p s)) M (weigh e p s M v F φ)
def pay := (s.L.val:ℝ)^h/(Fintype.card (Site s.L):ℝ)
theorem pay_pos : 0<pay s h:= by unfold pay; positivity
-- all preimages; in root coordinates
abbrev mean (V:Sketch G): Sketch G:= (pay s h) • (∑ z : Site s.L, pass e p s M z V)
-- lattice identity with chosen Theater
include T hp
lemma renewed (F:bore G) : freshen e p s M F=Delight.turn (crafts e p s T hp) e.x F M:= rfl
-- physics uses F(field) orientation course
include hs
lemma permits : ∃ a b:ℝ,∃ W:TableFee, (crafts e p s T hp).Rich ζ (2*ζ) a b W:= by
   obtain ⟨_,V,hV⟩:= T.banks hp; let F:=e.port p; have hf: Roof ζ F V:= ⟨fun i j=> (hV.shelter ..).weaken (terrain_le T.down) le_rfl⟩; obtain ⟨a,ha,H⟩:= T.base _ hs; exact ⟨a,1+a,V,hf,lt_of_lt_of_le T.light T.down,step_reserved ..,(H p).direct,ha, sky_shape (U:=e.A p s) (H p).feed ha, le_add_of_nonneg_right ha⟩
variable {e p s M}{v:Site s.L}{F:Sketch G}{x:Dye G}(hV:Living x M D F ζ)
include hV
lemma measure (φ:Cards): Based (2*ζ) x M (weigh e p s M v F φ):= by
   obtain ⟨a,b,W,h⟩:= permits e p s T hp hs; obtain ⟨H,U,hU⟩:= hV.lineage (desk s v φ); let z:=curb s v; have ht:=Theater.ecstasy (T:=crafts e p s T hp) h (migrant z H hU) (revised z hU) (step_reserved ..) x; exact ⟨ht.mounted,_,ht.up⟩
lemma know (φ:Cards): Based (2*ζ) x M (pass e p s M v F φ):= by obtain ⟨h,U,hU⟩:= measure T hp hs hV (v:=v) φ; let v:=sink e.x (e.kickoff p s); exact ⟨caring v h hU (sink_mast _),_,moving v _ hU⟩
end
end Transfer
end
end YM.Contacts.Harrier
