import YM.FormalBulk08.Rial.Ivory

/-! Exact finite orientation matrices for alphabet ($tion$). -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Rial
open Filter Set Function Lattice Laurent Wilson Exterior Stationary
open Orb Reef Jets Lava Lotus Mesa Gorge Shore City Kemp Rift Wine Pose PowerSeries Wick
open Planned.PrimaryIntegral295 Place Carrier Film Labels Source Source.Drops Next.Foundations Dawn
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {d n: ℕ} (F:Frame G d) (s : Signed)

lemma realTurn (u v:F.Index) : ↑((F.act s.ortho (copy F u) v).re) = F.act s.ortho (copy F u) v:= by
    apply Complex.conj_eq_iff_re.mp
    rw [show copy F u=F.coords (F.basis u) by rw [F.coords_basis];rfl, Frame.act_coords]
    change star (F.coords _ v)=_
    rw [← F.conj_basis,F.coords.symm_apply_apply,Labels.real_turn,F.realForm]
lemma exactGuard (u v:F.Index)(h:F.grades u≠F.grades v) : F.act s.ortho (copy F u) v=0:=by
    rw [show copy F u=F.coords (F.basis u) by rw [F.coords_basis]; rfl, Frame.act_coords]; apply F.power_coefficient v h; have hv := gradePart_mem (F.grades u) (tensor s.ortho (F.basis u)); rw [gradePart_turn, gradePart_self (F.basis u) _ (F.pure u)] at hv; exact hv

def fresh_pet (s:Signed)(k:Spring d) : Spring d:= ⟨breeze k.val s,(paper_is _).mpr ((breeze_h _ s).trans_le (paper_fits k))⟩
lemma pet_undo (k:Spring d) : fresh_pet s⁻¹ (fresh_pet s k)=k:= Subtype.ext (by
    change breeze (breeze k.val s) s⁻¹=k.val; rw [←spunk,mul_inv_cancel];rfl)
lemma pet_fwd (k:Spring d) : fresh_pet s (fresh_pet s⁻¹ k)=k:= by simpa using pet_undo s⁻¹ k

def Crew (x y:Letter F) := pet F y=fresh_pet s (pet F x) ∧ F.grades (mint F y)=F.grades (mint F x)
-- output x turned from input y (breadth preserves field-test split)
def lariat : Matrix (Letter F) (Letter F) Pence:= fun x y=>if Crew F s x y then PowerSeries.C (Dawn.tone (pet F x) s * (F.act s.ortho (copy F (mint F y)) (mint F x)).re) else 0
lemma crew_flip {x y:Letter F} : Crew F s x y ↔ Crew F s⁻¹ y x := by
    unfold Crew; constructor <;> rintro ⟨h,hx⟩ <;> refine ⟨?_,hx.symm⟩
    · rw [h, pet_undo]
    rw [h,pet_fwd]
lemma crew_rank {x y:Letter F}(h:Crew F s x y): Pose.slots F x=Pose.slots F y∧ label F x=label F y ∧ weight F x=weight F y:= by
   have hx:=congr_arg Prod.fst h.2
   refine ⟨congr_arg Prod.snd h.2.symm,hx.symm,?_⟩
   unfold Pose.weight; rw [h.1]; change _ = _ + Chapel.upper (breeze _ _);
   rw [breeze_h, show label F x=label F y from hx.symm]

def mates (x:Letter F):Finset (Letter F):=Finset.univ.filter (Crew F s x)
-- exact sum_bij on same field-grade index (other letters from that grade with same turned test)
def family (u:F.Index):Finset F.Index:= Finset.univ.filter fun a=> F.grades a=F.grades u

def next (x: Letter F) (k:F.Index)(h:F.grades k=F.grades (mint F x)) : Letter F:= ⟨(k,fresh_pet s (pet F x)), Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
   change (F.grades k).1+ Chapel.upper (breeze _ _) ≤ d; rw [breeze_h,h];exact weightFits F x⟩⟩
lemma next_member (x k h): Crew F s x (next F s x k h) := ⟨rfl,h⟩
lemma full_member {x y}(h:Crew F s x y): next F s x (mint F y) h.2=y := Subtype.ext (Prod.ext rfl h.1.symm)

lemma swims {α:Type*}[AddCommMonoid α](x:Letter F)(f:F.Index→α): ∑ y∈mates F s x, f (mint F y)=∑ y∈family F (mint F x),f y:=by
   classical
   refine Finset.sum_bij (fun i _=>mint F i) (fun i h=>?_) (fun a ha b hb e=>?_) (fun i hi=>?_) (fun _ _=>rfl)
   · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,((Finset.mem_filter.mp h).2).2⟩
   · exact Subtype.ext (Prod.ext e (((Finset.mem_filter.mp ha).2).1.trans ((Finset.mem_filter.mp hb).2).1.symm))
   exact ⟨next F s x i (Finset.mem_filter.mp hi).2,Finset.mem_filter.mpr ⟨Finset.mem_univ _,next_member ..⟩,rfl⟩
-- finite letter group reality; crossing E
lemma preserve (s:Signed)(T: Slate G d n)(U: Slate G d n)(hs:Monic T)(hu:Monic U)(hp : n ≤ d)(w : ℕ)(he:w ≤ d)(ht:∀ x,T x=U (turnIn G d s ∘ x)): lent T w=tensor s.ortho (lent U w):=by
    apply Subtype.ext; apply eval_ext; intro J; change Labels.read J (lent T w).val=Labels.read J (rotated _ _); rw [rotated, Labels.eval_changed,lent_pure hs he hp, lent_pure hu he hp,← WardBin.tile_reads,← WardBin.tile_reads]; apply congr_arg (WardBin.leading w); funext b
    let Z:=WardBin.engineered b (trunk d J); change tide T (fun _=>Z)= tide U _
    rw [tide_at,ht,tide_at]; congr 2; ext1 j; exact funext fun i=>map_smul (Taylor.turn s.ortho⁻¹) _ _
end YM.FormalBulk08.Rial
