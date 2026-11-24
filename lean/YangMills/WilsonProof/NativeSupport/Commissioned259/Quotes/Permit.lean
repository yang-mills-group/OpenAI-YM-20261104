import YangMills.WilsonProof.NativeSupport.Commissioned259.Quotes.Trial
/-! # The field-frame restrictions on all trials. Exact symmetry, also for the
unselected position equation. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Quotes
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score Comparing Pose Original Matrix
open Facets Reg.Point
open scoped Topology ContDiff Classical BigOperators Matrix
variable {I : Type*}{L:Filter I} {G : Gauge} {d n q m e : ℕ} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (U : Final C f S) (J Y : ℝ→PhysMS.tower S) (N : WilsonPrescription G) {A : ∀ d:ℕ, ℝ→Change G d} (t:ℝ→ℝ)
    (hJ:Leading U J) (P:Realized J Y N A t) (ν:ℝ)
    {sim : G.Simple} (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
local notation "late" => 𝓝[>] (0:ℝ)

/- For readability, the restrictions BUT NOW IN SEC coordinates. Preserve exact orientation
& phase laws at each cap, Eventually `trail` inherited from Leading. -/
structure Earns (r:ℝ) (e:ℕ) : Prop where
   rises : Original.heights U J r e
   real (v:Sec G e) : frame J r e (reel e v)=S.conj U.room.kernel.spin e (frame J r e v)
   signed (s:Signed)(v:Sec G e) : frame J r e (ori s.ortho e v)=S.mirror U.room.kernel.spin e s (frame J r e v)
   unit : frame J r e (leaf G e)= S.unit e

lemma field_bar (C : Family G) (v:(Bel C.book).Field d) : Free.fields C.labels d ((Bel C.book).conj (spin_free C.labels) _ v) = reel d (Free.fields C.labels d v) := Subtype.ext (Free.address_star C.labels v)
lemma field_ori (C : Family G)(v:(Bel C.book).Field d) (s:Signed) : Free.fields C.labels d ((Bel C.book).mirror (spin_free C.labels) _ s v) = ori s.ortho d (Free.fields C.labels d v) := Subtype.ext (Free.address_motion C.labels s v)
lemma field_unit (C:Family G) : Free.fields C.labels d ((Bel C.book).unit d)= leaf G d := Subtype.ext (Free.unit_address C.labels d)
lemma framing (C:Family G)(h:e≤d)(v:(Bel C.book).Field e) : Free.fields C.labels d ((scheme C.labels).rise h v) = up h (Free.fields C.labels e v) := Subtype.ext (Free.address_rise C.labels d h v)
lemma visits (j:tower S)(v : (Bel C.book).Field d) : frame (fun _=> j) 0 d (Free.fields C.labels d v) = j d v := by simp [Original.frame]
include hJ in
lemma earnings (d:ℕ) : ∀ᶠ r in late, Earns U J r d := by
  have hi r k (v:(Bel C.book).Field k) : frame J r k (Free.fields C.labels k v) = J r k v := visits (J r) _
  filter_upwards [height hJ d,hJ.equivariant d,hJ.unit d] with r hr hh hv
  refine ⟨hr,fun v=>?_,fun s v=>?_,?_ ⟩
  · obtain ⟨v,rfl⟩:= (Free.fields C.labels d).surjective v; rw [ ← field_bar, hi,hi]; exact hh.2 v
  · obtain ⟨v,rfl⟩:= (Free.fields C.labels d).surjective v; rw [ ← field_ori, hi,hi]; exact hh.1 s v
  rw [←field_unit C, hi]; exact hv
include hJ P in
lemma reapply (d:ℕ) : ∀ᶠ r in late,Earns U Y r d := by
  have h := Filter.eventually_all.mpr (fun i:Fin (d+1)=>P.relates i )
  filter_upwards [P.relates d, earnings U J hJ d,h] with r e h V
  refine ⟨ fun i hi v=>?_,fun v=>?_,fun s v=>?_,?_⟩
  · rw [e,P.stays,h.rises i]
    exact (congr_arg _ (V ⟨i,Nat.lt_succ_of_le hi⟩ v)).symm
  · rw [e, ← stood_reel,h.real,e]
  · rw [e, ← stood_ori,h.signed,e]
  rw [e,solitary,h.unit]
lemma earned_leads {r:ℝ} (e : Earns U J r d) : Spin.realH U.room.kernel.spin (Free.spin_free C.labels) (J r d) ∧
    (∀ j (h:j ≤ d)(v:(Bel C.book).Field j), J r d ((Maxwell.Free.scheme C.labels).rise h v) = U.sector.derivatives.rise h (J r j v)) ∧
    J r d ((Bel C.book).unit d) = S.unit d := by
  have hi k (v:(Bel C.book).Field k) : frame J r k (Free.fields C.labels k v) = J r k v := visits (J r) _
  refine ⟨⟨fun s v=>?_, fun v=>?_⟩,fun j h v=>?_,?_⟩
  · rw [ ← hi, ← hi,field_ori ]; exact e.signed ..
  · rw [ ← hi, ← hi,field_bar ]; exact e.real ..
  · rw [ ← hi, ← hi,framing ]; exact e.rises j h _
  rw [ ← hi,field_unit ]; exact e.unit
abbrev Allowed (X : FieldEnd G d) : Prop := X-1∈ Change G d
lemma eligible (X:FieldEnd G d) (V:∀ p:Sec G d,X (reel d p)=reel d (X p))
    (S:∀ (s:Signed)(p: Sec G d),X (ori s.ortho d p)=ori s.ortho d (X p)) (U: ∀ (e:ℕ)(h:e ≤ d)(p:Sec G e), (X (up h p)).val ∈ shellSector G e) (N:X (leaf G d)=leaf G d) : Allowed X := by
  refine may_change _ |>.mpr ?_ ; simp_rw [LinearMap.sub_apply,Module.End.one_apply]; rw [N]
  refine ⟨sub_self _,fun i hi v hv=>?_,fun p=>by rw [map_sub,V],fun s p=> by rw [map_sub,S] ⟩
  exact Submodule.sub_mem _ (U i hi (⟨_,hv⟩)) hv
-- transition between two towers, real (orbit) investments
abbrev personal (r s:ℝ) (d:ℕ) := (frame Y s d).trans (frame J r d).symm
lemma as_income (r s:ℝ) : Comparing.columns (personal J J r s d).toLinearMap= columns (via J r s d):= rfl
lemma personal_raises {r s:ℝ} (hx: Earns U J r d)(hy:Earns U Y s d) (h:e≤d)(v:Sec G e) :
    personal J Y r s d (up h v) = up h (personal J Y r s e v) := by apply (frame J r d).injective; rw [personal,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply, hx.rises e,hy.rises e, personal]; simp
lemma owns {r s:ℝ} (hx: Earns U J r d)(hy:Earns U Y s d) : Allowed (personal J Y r s d).toLinearMap := by
  apply eligible; rotate_left
  · intro v p; apply (frame J r d).injective
    simp only [personal, LinearEquiv.coe_coe,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,hx.signed,hy.signed]
  · intro i h v; exact (show ((personal J Y r s d) (up h v)).val∈_ from (personal_raises U J Y hx hy h v).symm ▸ (personal J Y r s i v).property )
  · simp only [personal, LinearEquiv.coe_coe,LinearEquiv.trans_apply,hy.unit]; rw [ ← hx.unit,LinearEquiv.symm_apply_apply]
  intro p; apply (frame J r d).injective
  simp only [personal, LinearEquiv.coe_coe,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,hx.real,hy.real]
-- D & base pay for Allowed exactly.
lemma engineer_allowed (s:ℝ) : Allowed (Level.Dial (G:=G) d s) := eligible _ (Level.Dial_real s) (fun v p=> Level.Dial_ori s v.ortho p) (fun i h v=> by rw [Level.chain]; exact Subtype.property (Level.Dial i s v) ) (Level.Dial_leaf s)
lemma allowed_from (x:Change G d) : Allowed (stand x) := by change 1+x.val-1 ∈_; rw [add_sub_cancel_left (1:Module.End ℂ (Sec G d)) x.val]; exact x.property
lemma allowed_product {V W:FieldEnd G d} (hx:Allowed V)(hy: Allowed W) : Allowed (V*W) := by
  let x: Change G d:=⟨_,hx⟩; let y: Change G d:=⟨_,hy⟩; obtain ⟨z,h⟩:=stand_times x y
  have f: V*W=stand z:= Eq.trans ?_ h; rw [f]; exact allowed_from _
  unfold x y stand; dsimp only; congr 1 <;> abel
lemma permitted (V:Normalize.Guard G d)(h:Base V)(p:ℕ)(v:ℝ) : Allowed (accepts V p v) := by
  induction p with
  | zero=> simp only [Allowed,accepts,Finset.sum_range_succ, Finset.sum_range_zero, zero_add,pow_zero,one_smul,h.zero]; exact (sub_self (1:Module.End ℂ (Sec G d))).symm ▸ (Change G d).zero_mem
  | succ p ih=>
    unfold Allowed; rw [accepts_first, ← Complex.ofReal_pow, add_sub_right_comm (a:=accepts V p v) (b:=(↑(v^ (p+1)):ℂ) • (coeff (p+1)) V) (c:=1)]; let s:= (Change G d); apply Submodule.add_mem s ih; exact s.smul_mem (v^(p+1)) (h.high _ (by omega))
include H
lemma trialAllowed (s:ℝ)(p:ℕ)(t:ℝ) : Allowed (accepts (guardTrial N ν M s d) p t) := by
  let z:= GroupS.gaugeN N.scheme N.criterion M ν s d; let D:= z*stepV (GroupS.ψ N.criterion M ν s) (Scale.mirror (Scale.Measure.adjust N.scheme N.criterion d)); have h:Base D := structure_trial N ν M H s
  rw [show accepts _ _ _=Level.Dial d s * accepts D p t from ?_]; exact allowed_product (engineer_allowed s) (permitted D h p t)
  simp only [accepts,guardTrial,conversion,mul_assoc, coeff_C_mul, Finset.mul_sum,mul_smul_comm]; rfl
end YM.FVA2.GradedFar259.Quotes
