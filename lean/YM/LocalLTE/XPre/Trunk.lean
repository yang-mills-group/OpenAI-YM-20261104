import YM.LocalLTE.XPre.Far
import YM.LocalLTE.XPre.Lamp
import YM.MergeProof.Cashew
import YM.MergeProof.Tuna
/-!
# Agenda recording entire analytic leaf costs and currency through
actual retained stamp. Label pin density QA.Later consumes this with
T.Tunes for grouped leaves and with perturbative horizons.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.XPre
open Function Finset Filter MeasureTheory Lattice Wilson RG
open Extra.Histories Push Local Motion Extra.Multi
open LocalLTE.Fan LocalLTE.River LocalLTE.Vinca
open PhysicalNext.Repeat Lotus Blush Progress.DirectedRecipe
open YM.MergeProof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {ι: Type}{G:Gauge}{c f:Side}{S:StepData c f} {R : Rep G f} {C: Rep G c}
    {κ K ν t u q r s b:ℝ} {A:Activities G f} {d p m l:ℕ} {o:Site f}{o':Site c}
open AbsoluteSums Animals Next.Foundations
variable {v w:ℂ}{X:Wing→Prop}{M:ι→ Leaf R}{g:ι→ℂ}{φ:MergeProof.Response G c}{L:GaugeDoor R C}
local notation "F₁"=> Config G f→ ℂ
variable {E:Config G f→ℂ} {Z: Res G f}{W : Res G c}
-- cost t bounds both.E. Additional Magn lane.F.H v Unit costs.
-- Excluded cost ψB only Nonread.Answer permits closed log.Frame. Δ from shifting Beacon.
open Menu Marker
variable [Countable ι]{ξ Q:ℝ}(B:Finset ι)
local notation "U"=> {i:ι//i ∉ B}
local notation "T'"=> (B:Set ι)ᶜ
omit [Countable ι] in
lemma together {F:Type}[NormedAddCommGroup F][CompleteSpace F] {g:ι→F}{v:F}(hp:HasSum g v): v= (∑ i:↥B,g i.val)+ ∑' i: U,g i.val:=by
    rw [Finset.sum_coe_sort]; exact (hp.summable.sum_add_tsum_compl.trans hp.tsum_eq).symm
omit [Countable ι] in
lemma tailless {f:ι→ℝ}(h:SumBudget f ξ)(ht:0<t):∃ T:Finset ι, SumBudget (fun i:{i//i∉T}=> f i.val) t:=by
   obtain ⟨s,hT⟩:= ((tendsto_tsum_compl_atTop_zero f).eventually (gt_mem_nhds ht)).exists
   exact ⟨s,fun i=> h.1 _,h.2.1.comp_injective Subtype.val_injective, hT.le⟩
set_option quotPrecheck false
variable (h: Odyssey X o o' 1 E Z W w t u L M g φ)(P:ι→Prop)(hp:SumBudget (tollNon P M g) Q)
local notation "r0"=> fun i=> ‖g i‖*load (M i)
-- need earn support.
include h
omit [Countable ι] in
lemma split_tails (hX:SumBudget (fun i:U=> ‖g i.val‖*load (M i.val)) ξ): Odyssey X o o' 1 (E-∑ i:↥B, g i.val • prose (M i.val)) (Z-∑ i:↥B,g i.val • entry (M i.val)) (W-∑ i:↥B,g i.val • quoted L (M i.val)) w ξ u L (fun i:U=>M i.val) (fun i=> g i.val) φ:=by
    refine ⟨fun i=>h.member i.val,hX,h.cost,fun V=> ?_,fun p V=>?_,fun p V=>?_⟩
    · -- E. P normalization: use generic sum; cannot omit.
      have h' := together B (h.lyric V)
      let f (i:ι):= g i * prose (M i) V; have hh : Summable fun i:U=> f i.val:= (h.lyric V).summable.comp_injective Subtype.val_injective
      simp only [Pi.sub_apply, Finset.sum_apply,Pi.smul_apply,smul_eq_mul]; change HasSum (fun i:U=>f i.val) _; rw [sub_right_comm,h']; convert hh.hasSum using 1; abel
    · have h':= together B (h.old p V)
      let f (i:ι):= g i*entry (M i) p V; have hh:Summable fun i:U=>f i.val:= (h.old p V).summable.comp_injective Subtype.val_injective
      simp only [Pi.sub_apply, Finset.sum_apply,Pi.smul_apply,smul_eq_mul]; rw [h']; convert! hh.hasSum using 1; abel
    have he := h.grants p V; simp_rw [one_mul] at he; have h':= together B he; let f(i:ι):= g i * quoted L (M i) p V; have hh: Summable fun i:U=>f i.val:= he.summable.comp_injective Subtype.val_injective
    simp only [one_mul,Pi.sub_apply, Finset.sum_apply,Pi.smul_apply,smul_eq_mul];rw [sub_right_comm,h'];convert! hh.hasSum using 1; abel

variable {J:Type}[DecidableEq J] (R': Marker.Census J)
variable (j:J)(ℓ: J→ℝ) (hJ:∀ i,0<ℓ i) {l':ℕ} -- N wards
noncomputable def active (R':Marker.Census J)(M:ι→ Lotus.Leaf R)(g:ι→ℂ) (j:J) (i:ι):Hat R' R:= { M:=M i, s:=R'.fire j, charge:=g i, shiny:=Finset.singleton_nonempty j }
local notation "Bc"=> B.filter (fun i=>P i)
local notation "Z'"=> ↥Bc
-- This before E.P.Receipts.
include h
local notation "Xρ"=> XPhase.packer
-- if hT tail only NEED tail of analytic.Pay.At includes rest.ERROR.
-- return a challenge for ANY listed hat coefficient.N.
variable (hB : ∀ i,P i → Reader R d κ p l (M i))
variable (T: ℝ)
variable (hm:SoundDoor S L)(hx:Tunes L)(hX : (setOf X).Finite)
include hp hB hJ hm hx hX -- X: Wing→Prop need Set.
lemma munition (hr:SumBudget (fun i:U=> ‖g i.val‖*load (M i.val)) T):
    let c:=B.filter (fun i=>P i); let q:= fun i:↥c=> XPre.active R' M g j i
    let v:= Q+T
    ∃ (I:Type) (_: Fintype I) (q': I→Menu.Hat R' R), let N:= Sum.elim q q'; let p':= fun i: (↥c⊕I)=> i.isLeft
      (∀ i,(N i).s=R'.fire j ∧ o∈ (N i).M.crest) ∧ (∀ i,p' i=true→ Reader R d κ p l (N i).M)∧ (∑ i:↥c,R.p.mass (q i).M.crest (Menu.fare (q i) ℓ))≤ ℓ j*t ∧ (∑ i:I,R.p.mass (q' i).M.crest (Menu.fare (q' i) ℓ))≤2*ℓ j*v∧ (∀ Ux,∑ j, odour (N j) Ux= Poly.send (R'.fire j) (E Ux-w))∧ (∀ i Ux,∑ j, fragrance (N j) Ux i=Poly.send (R'.fire j) (Z i Ux))∧ ∀ p Ux,(∑ i, owl (N i) L j p Ux)= W p Ux-hook C.activities C.p.threshold φ p Ux:=by
    intro c q v; let f(i:ι):= ‖g i‖*load (M i); let u:={i//i∈c}
    have hf:SumBudget f t:= h.purchase; have hh: c⊆B:=Finset.filter_subset ..
    have hb' : SumBudget (fun i:{i//i∉c}=> f i.val) v:=by
       let g (i:ι):= tollNon P M (show ι→ℂ from g) i; have he:(∑ i∈ B\c,f i)=(∑ i∈B\c,g i):=by
           refine sum_congr rfl fun i hi=>?_ ; obtain ⟨ha,hx⟩:= mem_sdiff.mp hi; exact (if_neg (show ¬P i from fun h=>hx (mem_filter.mpr ⟨ha,h⟩))).symm -- annotation g not defin
       let t:=∑' i,f i; let T'':=∑ i∈ c,f i; have hc:t=T''+∑' i:{i//i∉ c},f i.val:= hf.2.1.sum_add_tsum_compl.symm; have hB : t= (∑ i∈ B,f i)+∑' i:U,f i.val:= hf.2.1.sum_add_tsum_compl.symm
       rw [← sum_sdiff hh,he] at hB -- lemma name
       refine ⟨fun i=> hf.1 _, hf.2.1.comp_injective Subtype.val_injective,?_⟩
       have hh : ∑ i∈B\c,g i≤ Q:= Extra.Multi.Budget.cap hp _; have he: ∑' i:U,f i.val ≤ T:=hr.2.2; unfold v; unfold T'' at hc; linarith only [hh,he,hc,hB]
    obtain ⟨I,hI,N,hsN,hQ,hE,hZ,hP0⟩:= Menu.narrow1 R' j (split_tails c h hb') hX hm hx hJ
    refine ⟨I,hI,N,?_,?_,?_,hQ,?_,?_,?_⟩
    · rintro (i|i); exact ⟨rfl,(h.member i.val).1⟩; exact hsN _
    · rintro (i|i) he; exact hB _ ((mem_filter.mp i.property).2); exact False.elim (Bool.noConfusion he)
    · let σ i:= ‖(g i)‖*(load (M i)); have he(i:↥c):R.p.mass (q i).M.crest (Menu.fare (q i) ℓ)= ℓ j * σ i.val:=by unfold q XPre.active Menu.fare BudgetPoint.mass σ; dsimp only; rw [sumFee]; dsimp only; rw [Poly.solo_toll]; unfold load BudgetPoint.mass; ring
      simp_rw [he];rw [← mul_sum,Finset.sum_coe_sort]; exact mul_le_mul_of_nonneg_left (Extra.Multi.Budget.cap h.purchase _) ((hJ j).le)
    · intro Ux; rw [Fintype.sum_sum_type]; change (∑ i:↥c,_ )+(∑ i,odour (N i) Ux)=_; rw [hE Ux]
      ext i; rw [Poly.part_plus,Poly.part_sum]; unfold odour; dsimp only [q,XPre.active,Sum.elim_inl]; simp_rw [Poly.part_send]; split_ifs with heI
      · simp only [Pi.sub_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]; simp_rw [mul_comm (prose _ _ )]; abel
      rw [Finset.sum_const_zero,add_zero]
    · intro k Vx; rw [Fintype.sum_sum_type]; change (∑ i:↥c,_) + (∑ i, fragrance (N i) Vx k)= _; rw [hZ k Vx]
      ext i; rw [Poly.part_plus, Poly.part_sum]; unfold q fragrance; dsimp only [XPre.active,Sum.elim_inl]; simp_rw [Poly.part_send]; split_ifs with heI
      · simp only [Pi.sub_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]; simp_rw [mul_comm (entry _ _ _)]; abel
      rw [Finset.sum_const_zero,add_zero]
    intro k Vx; rw [Fintype.sum_sum_type]; change (∑ i:↥c,_) + (∑ i, owl (N i) L j k Vx)= _; rw [hP0 k Vx]
    unfold q owl; dsimp only [XPre.active,Sum.elim_inl]; simp only [if_true,Pi.sub_apply, Finset.sum_apply,Pi.smul_apply,smul_eq_mul]; abel
end YM.LocalLTE.XPre
