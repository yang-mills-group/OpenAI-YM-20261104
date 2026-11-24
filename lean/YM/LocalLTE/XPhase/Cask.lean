import YM.LocalLTE.XPhase.Rare
/-!
# K*Closure re-expression. Log carries small across mixed-gen mask changes.
 The field HERE holds the same vacuum and conditional normalization: the
 singleton equation must be verified again with the aligned `GaugeDoor`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.XPhase
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open MergeProof Accent GridApprox.Nil Extra.Trajectories Extra.Multi
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V J : Type}[DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
variable {w: V→ℝ} {t d A₀ c W s g e v y:ℝ} {N:ℕ}
variable [Fintype V] (B:Census V)(R:Rep G n) (K:Box n→Config G n→Poly B) (F:Config G n→Poly B) (ψ:V→ Response G n)
variable [Fintype J] (X:J→Support n)(f:J→Config G n→Poly B)
variable {o:V→Site n}
-- one closure plus all shutters. 
abbrev RearC (V:Type) [DecidableEq V](J:Type) (B:Marker.Census V) (n:Side):= (V × Support n) ⊕ (Rising B × J)
abbrev unitsR := (Sum.elim (conviction ψ B) (packer f))
abbrev layoutR := Sum.elim (fun i: V × Support n=>i.snd) (fun j:Rising B × J=> X j.2)
local notation "Λ"=> unitsR B ψ f
local notation "F₀"=> Accent.closure K (unitsR B ψ f) (layoutR B X) R.p.threshold
-- The mixed f supplied once per support; no repeated test variable. Δ treated at full mask.
local notation "Zx"=> RearC V J B n
local notation "β"=> R.p.threshold
local notation "b"=> R.p.B
local notation "ρ"=> R.p.supportExponent
local notation "ε"=> R.p.supportExponent+1
variable (hx:Garnish R.p o ψ w (R.p.supportExponent+1) c)(hf:Towed w X f R.p.B (R.p.supportExponent+1) s)(hg:∀ i,Borne o (X i) (f i) R.p.threshold)(ht:∀ j U,rises (f j U)) (hH:∀ i U,Healthy R.p.threshold (X i) U→f i U=0)
variable (hP:Towed w Prod.fst K R.p.B (R.p.supportExponent+1) W)(hK:∀ i,Flow o i (K i) R.p.threshold)(hz:∀ i U,(K i U).part B.quiet=profile R.activities (fun j=>Complex.ofReal ∘ R.activities.K j) i U)
include hx hg ht hH hK
omit ht hg hK [Fintype V] [Fintype J] in
lemma boosted (U:Config G n) (i:RearC V J B n): (unitsR B ψ f) i U≠0→¬ Healthy R.p.threshold (layoutR B X i) U:=by
   cases i with
   | inl i=> exact Accent.husk ψ B hx i U
   | inr i=> rintro hp ht; exact hp (show (packer f i U)=0 from (by unfold packer; rw [hH i.2 U ht,Poly.part_nil]; exact Poly.send_zero _))
omit hx hg ht hH hK
omit [Fintype V] [Fintype J] in
lemma stamped (U:Config G n): ∀ z: RearC V J B n,(Λ z U).part B.quiet=0:=by
   intro z; cases z with
   | inl s=> exact corn_quiet ψ B U _
   | inr s=> change (packer f s U).part _=0; unfold packer; rw [Poly.part_send,if_neg (show B.quiet ≠ s.1.val from (fun h=> by have he:=s.1.property; rw [← h] at he; simp [Census.quiet] at he))]
include hK ht hH hx
-- constructor.B. compute mixed exponent after extraction.
abbrev receipts : Config G n→Poly B:= fun U=> kelp ψ B U+∑ j:J,f j U
local notation "Ω"=> receipts B ψ f
omit hx hH hK in
lemma layered_state (U:Config G n): (∏ i: RearC V J B n, (1+Λ i U))= Poly.pass (receipts B ψ f U):=by
    let tag: RearC V J B n→ B.Mode:= Sum.elim (fun j=> B.fire j.1) (fun j=> j.1.val)
    let chi: RearC V J B n→ℂ:= Sum.elim (fun j=> ψ j.1 j.2 U) (fun j=> (f j.2 U).part (j.1.val))
    have hZ (i): Λ i U= Poly.send (tag i) (chi i):=by rcases i with i|i <;> rfl
    -- Invert pass_sum
    have H := pass_sum (R:=B) Finset.univ tag (fun i _=> match i with | .inl j=> Finset.singleton_nonempty _ | .inr j=> Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0<2) j.1.property)) chi
    simp_rw [←hZ] at H; rw [Fintype.sum_sum_type] at H; -- may let type.S
    have h:= H.symm; exact h.trans (congr_arg Poly.pass (congr_arg₂ _ rfl (XPhase.packed f (fun j=> ht j U))))
omit hx hH hK in
lemma additiveR (U:Config G n) : (receipts B ψ f U).part B.quiet=0 ∧ (∀ i:B.Mode,2≤ i.val.card → (receipts B ψ f U).part i=(∑ j:J,f j U).part i):=by
    constructor
    · unfold receipts; rw [Poly.part_plus]; rw [show (kelp ψ B U).part B.quiet=0 from ?_, Poly.part_sum, Finset.sum_eq_zero (fun i _=> hop B _ (ht i U)),add_zero]; simp only [kelp,Poly.part_sum,corn_quiet ψ B U,Finset.sum_const_zero]
    intro i hp; unfold receipts;rw [Poly.part_plus,kelp,corn_light ψ _ hp U,zero_add] -- order edit
lemma caskP (U:Config G n)(hF:(F U).part B.quiet=0): play R B K F U= play R B (Accent.closure K (unitsR B ψ f) (layoutR B X) R.p.threshold) (F-Ω) U:=by
    have hh:field (fun i=> F₀ i U) (flags R.p.threshold U) = field (fun i=> K i U) (flags R.p.threshold U)*Poly.pass (Ω U):=by
       rw [Accent.allclosed K (unitsR B ψ f) (layoutR B X) R.p.threshold U (fun i hi=> (hK i|>.permits U hi).2) (fun i=> XPhase.boosted B R ψ X f hx hH U i)]
       rw [XPhase.layered_state B ψ f ht U] -- some unnecessary incl.
    unfold play; rw [hh]
    have ho:= (XPhase.additiveR B ψ f ht U).1
    have hp : (F U-Ω U).part B.quiet=0:=by rw [part_sub,hF,ho,sub_zero]
    nth_rw 1 [show F U = (F U-Ω U)+Ω U from (sub_add_cancel ..).symm]; rw [pass_add hp ho, Pi.sub_apply]; ring_nf
variable (k':V→ℕ→Config G n→ℂ)(hp':∀ i j U,(K i U).part (B.fire j)+hook R.activities R.p.threshold (ψ j) i U=profile R.activities (k' j) i U)
variable (hA:R.activities.Valid R.p e v)(u:ℝ)(hu:0<u)(h1:u≤1)(hq:∀ i,0<w i)(he:Occupancy o N)(hc:0 ≤ c)(hu':((R.p.B+R.p.B+1:ℕ):ℝ)^4*(W/u+ ((N:ℝ)*siteFactor R.p.B*c+s))≤1)
include hg ht hH hf hx hz hA hP hu h1 hq he hc hu' hp'
local notation "ν"=> u*(Real.exp (W/u+ ((N:ℝ)*siteFactor R.p.B*c+s))-1)
omit ht hH in
lemma blessed : (∀ i,Flow o i (F₀ i) β) ∧ (∀ i U, (F₀ i U).part B.quiet= profile R.activities (fun j=> Complex.ofReal ∘ R.activities.K j) i U) ∧ (∀ i j U,(F₀ i U).part (B.fire j)= profile R.activities (k' j) i U) ∧ Towed w Prod.fst (F₀) b ρ (ν):=by
    have hv(i: RearC V J B n): Borne o (layoutR B X i) (Λ i) β:= by cases i with | inl i=> exact Accent.dresses ψ B hx i| inr i=> exact XPhase.pack_b f X hg i
    have h(i: RearC V J B n) U:(Λ i U).part B.quiet=0:= stamped B ψ f U i
    refine ⟨fun i=>threshed K Λ (layoutR B X) β hK hv i,fun i U=>?_,fun i j U=>?_, branch_scaled K Λ (layoutR B X) u β hu h1 hP (XPhase.crew (Accent.stock ψ B hx hq he hc) (XPhase.pack_ledger f X hq hf)) hq R.p.exponent_pos.le hu'⟩
    · exact (Accent.wine K Λ (layoutR B X) β U i (fun i=>hK i|>.permits U) (fun i=>h i U)).trans (hz i U)
    rw [Accent.snow K Λ (layoutR B X) β U i (fun i=> (hK i|>.permits U)) _ (fun i=>hz i U) (fun i=>h i U) j (mass_crest _ hA U)];rw [Fintype.sum_sum_type]; let Y₀ := Rising B × J
    have hv' (i:Y₀) : ((Λ (.inr i)) U).part (B.fire j)=0:= by
       have ha:B.fire j ≠ i.1.val:=by intro a; have h := i.1.property; rw [← a] at h; simp [Census.fire] at h
       exact (show (packer f i U).part _=0 from by unfold packer; rw [Poly.part_send,if_neg ha])
    have ht' : ∑ j':Y₀,(Λ (.inr j') U|>.part (B.fire j))* portion R.activities β (layoutR B X (.inr j')) i U=0:= sum_eq_zero (fun i _=> by rw [hv' i,zero_mul]) -- h invisible. 
    rw [show (∑ j':Y₀, (_ :ℂ))=0 from ht', add_zero]; -- placeholder unify
    refine ((congr_arg ((K i U|>.part (B.fire j)) + ·) ?_).trans (hp' i j U)); change ∑ z',(conviction ψ B z' U|>.part (B.fire j))* portion R.activities β z'.2 i U = _; rw [Fintype.sum_prod_type,sum_eq_single j]; unfold hook; simp [conviction]
    · intro bY _ hb; simp [conviction,hb.symm]
    simp
end YM.LocalLTE.XPhase
