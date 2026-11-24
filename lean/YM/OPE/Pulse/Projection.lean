import YM.OPE.Pulse.Kiln
import YM.OPE.Grouping.Birth

/-!
# Projection-of-product with old unit charges held over
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.Fibers
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J : Type*} [DecidableEq V][Fintype V] [DecidableEq I][Fintype I]
variable (Δ : Fibers I V)
-- used also by Grid coupling
abbrev mark (s:Finset V) : (Bud V).Mode:=⟨s,Finset.mem_univ _⟩
lemma part_send_mul (s t:Finset V) (Q:Poly (Bud V))(b:ℂ) :
    (Q*Poly.send (mark t) b).part (mark s) = if t⊆s then Q.part (mark (s\t)) * b else 0:=by
   rw [Poly.part_mul]; let f (i j:(Bud V).Mode) := if Poly.merges i j (mark s) then Q.part i * (Poly.send (mark t) b).part j else 0
   have he (i : (Bud V).Mode) : ∑ j, f i j=f i (mark t) := by
     rw [sum_eq_single (mark t)]; intro j _ hj; unfold f; simp only [Poly.part_send,if_neg hj]; split <;> simp
     simp
   have hx (i:(Bud V).Mode) : Poly.merges i (mark t) (mark s) ↔ t⊆s ∧ i=mark (s\t):=by
      change Disjoint i.val t ∧ i.val∪t=s ↔ _; constructor
      · rintro ⟨h,rfl⟩; refine ⟨subset_union_right,Subtype.ext ?_⟩; simp only [Finset.union_sdiff_right]; exact (Finset.sdiff_eq_self_of_disjoint h).symm
      rintro ⟨h,rfl⟩; exact ⟨Finset.sdiff_disjoint,Finset.sdiff_union_of_subset h⟩
   have hv (i:(Bud V).Mode) : f i (mark t) = if t⊆s then (if i=mark (s\t) then Q.part i*b else 0) else 0:= by
      unfold f; simp [hx,ite_and]
   change (∑ i,∑ j,f i j)=_; simp_rw [he,hv]; split <;> simp
lemma reap_dec (Q: Poly (Bud I))(v:V)(b:ℂ) (he:Δ.Only v) : Δ.reap (Q*Poly.send ((Bud I).fire (Δ.twig v)) b) = Δ.reap Q*Poly.send ((Bud V).fire v) b:=by
    ext s; let t:= (Δ.plena s).val
    have hm : ({Δ.twig v}:Finset I)⊆ t ↔ ({v}:Finset V)⊆ s.val:= by rw [singleton_subset_iff,singleton_subset_iff, Δ.reaped,Δ.sectioned]
    have hz : (Δ.plena (mark (s.val\{v}))).val=t\{Δ.twig v}:=by
       ext i; rw [Δ.reaped]; change Δ.bunch i∈ s.val\{v} ↔ _
       rw [Finset.mem_sdiff,Finset.mem_sdiff,Δ.reaped]; simp only [mem_singleton]; rw [show Δ.bunch i=v ↔ i=Δ.twig v from ⟨fun h=>he.again ((Δ.focuses ..).mpr h),fun h=> h.symm ▸ Δ.sectioned v⟩]
    have h (s:(Bud V).Mode): (Δ.reap Q).part s=Q.part (Δ.plena s):= rfl
    change (Q*Poly.send (mark _) b).part (mark t)=(Δ.reap Q*Poly.send (mark _) b).part (mark s.val); rw [part_send_mul,part_send_mul]; simp only [hm,h,show Δ.plena (mark (s.val\{v}))=mark (t\{Δ.twig v}) from Subtype.ext hz]
lemma reap_campaign (s:Finset V) (u:I→ℂ)(Q: Poly (Bud I)) (h:∀ i∈s,Δ.Only i) : Δ.reap (Q*Poly.pass (∑ i∈s,Poly.send ((Bud I).fire (Δ.twig i)) (u (Δ.twig i)))) = Δ.reap Q * Poly.pass (∑ i∈s,Poly.send ((Bud V).fire i) (u (Δ.twig i))):=by
    simp_rw [pass_sum s (tag:=fun v=>(Bud I).fire (Δ.twig v)) (fun v _=>singleton_nonempty _), pass_sum s (tag:= (Bud V).fire) (fun v _=>singleton_nonempty _)]
    induction s using Finset.induction_on with
    | empty=>simp
    | @insert a s ha IH=>
       rw [prod_insert ha,prod_insert ha,mul_comm (1+_),mul_comm (1+_),← mul_assoc,← mul_assoc]
       rw [mul_add,mul_add,mul_one,mul_one,map_add]
       rw [reap_dec Δ _ _ _ (h _ (mem_insert_self ..)), IH (fun i hi=> h i (mem_insert_of_mem hi))]
lemma camp_zero (s:Finset V)(v:V→ℂ) : (∑ i∈s,Poly.send ((Bud V).fire i) (v i)).part (Bud V).quiet=0:=by rw [Poly.part_sum]; apply sum_eq_zero; intro i _; simp [(Bud V).fire_hot i|>.symm]
lemma camp (s:Finset V)(v:V→ℂ) : (∑ i∈s,Poly.send ((Bud V).fire i) (v i))= Mach (Bud V) (fun i=> if i∈s then v i else 0):=by
    unfold Mach
    calc _ = ∑ i∈s,Poly.send ((Bud V).fire i) (if i∈s then v i else 0):=sum_congr rfl fun i hi=> by rw [if_pos hi]
         _ = _ := sum_subset (subset_univ _) fun i _ hi=> by rw [if_neg hi, Poly.send_zero]
def rebate (s:Finset V)(u:I→ℂ)(k:I):ℂ:= if k∈s.image Δ.twig then 0 else u k
def recovered (s:Finset V) (u:I→ℂ) (v:V):ℂ:= if v∈s then u (Δ.twig v) else 0
lemma refund (s:Finset V) (u : I→ℂ) : Mach (Bud I) u=Mach (Bud I) (rebate Δ s u) + ∑ i∈s,Poly.send ((Bud I).fire (Δ.twig i)) (u (Δ.twig i)):=by
    unfold Mach
    let T:= s.image Δ.twig
    let Q i:= Poly.send ((Bud I).fire i) (u i)
    change ∑ i,Q i=_+ ∑ i∈s,Q (Δ.twig i)
    rw [← Finset.sum_image Δ.sectioned.injective.injOn, camp (s.image Δ.twig), Mach, ← sum_add_distrib]
    refine sum_congr rfl fun i _=>?_ ; unfold Q rebate; split <;> simp_all
namespace Salt
variable {V I:Type}[DecidableEq V] [DecidableEq I][Fintype V][Fintype I]{Δ : Fibers I V}
variable {n:Side}{G:Gauge} (R:Rep G n) (S:Salt V I Δ G n)
local notation "τ" => R.p.threshold
lemma reimbursed (U:Config G n)(s:Finset V)(u : I→ℂ) (hc:S.pepper=Δ.rebate s u) (h:S.Breeze R.p.threshold)(he:∀ i∈s,Δ.Only i) :
    Fibers.reap Δ (play R (Bud I) S.river (fun U=> Mach (Bud I) u+ ∑ i,S.air i U) U)=
      play R (Bud V) (S.soil R.p.threshold) (fun U=> Mach (Bud V) (Δ.recovered s u) + ∑ i,S.mount R.p.threshold i U) U:=by
    let A₀:= (Mach (Bud I) S.pepper+ ∑ i,S.air i U)
    let A₁:= (Mach (Bud V) (Δ.recovered s u) + ∑ i,S.mount R.p.threshold i U)
    have hv := Δ.reap_campaign s u (Poly.pass A₀* field (fun i=>S.river i U) (flags τ U)) he
    have hz : A₀.part (Bud I).quiet=0:=by unfold A₀; rw [Poly.part_plus,mute,zero_add,Poly.part_sum]; exact sum_eq_zero fun j _=> (h.home j).sil _
    have hx:(∑ i∈s,Poly.send ((Bud I).fire (Δ.twig i)) (u (Δ.twig i))).part (Bud I).quiet=0:=by rw [Poly.part_sum]; apply sum_eq_zero; intro i _; simp [((Bud I).fire_hot (Δ.twig i)).symm] -- simp tactic dot notation ellipsis?
    have hy:(∑ i,S.mount τ i U).part (Bud V).quiet=0:= by rw [Poly.part_sum]; apply sum_eq_zero; exact fun i _=> ((S.vessel τ).clearBurn _ (S.wet _ h) (S.turn _ h) i).sil _
    unfold play; dsimp only; rw [map_smul, refund Δ s u, ← hc, add_right_comm, pass_add hz hx, mul_right_comm, hv]; simp_rw [camp s (v:=fun i=>u (Δ.twig i))]; rw [pass_add (mute ..) hy]; unfold recovered; unfold A₀; rw [S.yields _ U h]; ring_nf
end Salt
end YM.MergeProof.Ribbons.Fibers
