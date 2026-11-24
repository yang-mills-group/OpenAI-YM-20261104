import YM.LocalLTE.Dilation.Reserve
/-!
# Re-render on this same Actual. Flag-Updates after expansion of bulk supports.

Cost exposes layout inflation but leaves knobs PRE-Column-issuance. ALL budgets
for reality checked again, especially support strips where the flag pattern
flips. `Hook` recipe for playing with MULTIPLE such sources in this exact
layout. Uses actual sqrt-divisor. `Stamper` carries guarantees on the precise
Voice contributions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Dilation
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Next.Foundations
open Planned.GuardedAtom Guard Push Local YM.MergeProof
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side}{ι:Type*}{d:ℕ}{F:Labels.Frame G d}{o:Site n}{B:SectionData F}
    {R:Rep G n}
variable {P:BudgetPoint} {A:Hol G} {σ C Λ δ η w e r v g a b c d' t : ℝ}
-- Hilde.Band. Metadata criteria independent of analytic answer at output.
structure Fills (o:Site n) (X Y:ℕ→Support n) (P:BudgetPoint) (m:ℝ) : Prop where
    factor: 1 ≤ m
    broad j: X j ⊆ Y j
    thin j: Nonwrapping (X j) o → Nonwrapping (Y j) o
    charges i t : 0≤ t → reservedMass P (Y i) t ≤ m* reservedMass P (X i) t
variable {X Y:ℕ→Support n}
def update (P:BudgetPoint) (X Y:Support n) (f:Config G n→ℂ):= masked P.threshold X f-masked P.threshold Y f
lemma maskAdapt {X Y:Support n}(h:X ⊆ Y){f:Config G n→ℂ}(hf:P.Regular X f) : Attaches P.threshold Y (update P X Y f)∧
    ∀ o e,P.supBounds o X f e →∀ U, ‖update P X Y f U‖ ≤ e:=by
    let t:=P.threshold
    have he:= regular_larger hf h; let u:= update P X Y f
    have hp U : Healthy t Y U → u U=0:=fun hY=> by simp only [u,update,Pi.sub_apply,show P.threshold=t from rfl,masked_eq _ _ _ _ hY,masked_eq _ _ _ _ (Finset.disjoint_of_subset_left h hY),sub_self]
    refine ⟨⟨fun U V hX ht=> ?_,fun η i=> ?_,(masked_measurable _ _ _ hf.borel).sub (masked_measurable _ _ _ hf.borel),hp⟩,fun o e hE U=>?_⟩
    · exact congr_arg₂ (·-·) (Work.H03.reads_larger h (uses_mask t hf.sites) U V hX ht) (uses_mask t he.sites U V hX ht)
    · exact congr_arg₂ (·-·) (invariant_mask hf.symmetry t X η i) (invariant_mask he.symmetry t Y η i)
    by_cases hY: Healthy t Y U
    · change ‖u U‖ ≤ e; rw [hp U hY,norm_zero]; exact hE.1
    unfold update; rw [Pi.sub_apply,masked_ne _ _ _ _ hY,sub_zero]; by_cases hX:Healthy t X U
    · rw [masked_eq _ _ _ _ hX]; exact hE.2 U hX [] (Nat.zero_le _) (by simp)
    rw [masked_ne _ _ _ _ hX,norm_zero]; exact hE.1
variable (X) (M:Local.Raw F n) (S:Berths R.p R.activities Y)
def off := fun i=> update R.p (X i) (Y i) (M.bulk i)
def out : Local.Raw F n:= {M with forced := M.forced+rented S (fun i=> update R.p (X i) (Y i) (M.bulk i))}
local notation "W"=> out X M S
local notation "Ω" => hitWidth R.p * w
local notation "θ"=> (fun i=> update R.p (X i) (Y i) (M.bulk i))
-- δ.Separate estimate from true Layout.On B.Read only canonical.
variable (h:Fills o X Y R.p g) (hx:R.Lawful σ C Λ δ w)(hw:0 ≤ w) (hq:hitWidth R.p * w ≤ 1) (hr: Local.Readable A B R.p n e) -- notation macro §
    (hk :0 < r) (hf:M.Format o X R) (hu : YM.Planned.GuardedAtom.Deck M o X R r a b)
local notation "ε"=> Ω /r
set_option quotPrecheck false
include h hx hw hq hk hf hu
lemma ledger : Attainment R.p o (clipSum Y θ) (g*a) ∧ profile R.activities (W).forced=profile R.activities M.forced + hook R.activities R.p.threshold (clipSum Y θ) ∧
    (W).Format o Y R ∧ (W).eval o Y B R=M.eval o X B R ∧ YM.Planned.GuardedAtom.Deck (W) o Y R r (g*a) (b+ ε*(g*a)):=by
    obtain ⟨u,hU,hT⟩:= hu.bulk; let f i:= update R.p (X i) (Y i) (M.bulk i)
    have he i:= maskAdapt (h.broad i) (hf.regular i)
    have huP i : 0 ≤ u i ∧∀ U,‖f i U‖ ≤u i:= ⟨(hU i).1,he i|>.2 _ _ (hU i)⟩
    have hP i:= h.broad i (hf.origin i)
    have hs:SumBudget (fun i=> reservedMass R.p (Y i) (u i)) (g*a):= sumBudget_mono (Local.sumBudget_mul_left hT (zero_le_one.trans h.factor)) (fun i=> mul_nonneg (Real.exp_pos _).le (huP i|>.1)) (fun i=> h.charges _ _ (huP i|>.1)) le_rfl -- ambig
    obtain ⟨hB,hE,hD,hA,hK⟩:= Dilation.cover S f (fun i=> (he i).1) hP u huP hs hx hw hq
    let q:= (W).forced
    let l:= rented S f; have hi:q = M.forced + l:=rfl
    have hl:Dominated l:=by obtain ⟨a,ha,hq⟩:=hE; exact ⟨_,ha.2.1,fun i U=> (hq i|>.2 U).trans (R.p.loMass _ _ (hq i|>.1))⟩
    have hp:Dominated M.forced:= limb hu.packets
    refine ⟨hA, ?_, ⟨hP, fun i=> regular_larger (hf.regular i) (h.broad _), hf.force.add hB⟩, ?_, ⟨⟨u,fun i=> bound_larger (hU i) (h.broad i),hs⟩,?_⟩⟩
    · change profile R.activities q = _; change profile R.activities l= hook R.activities _ (clipSum Y f) at hD
      rw [show θ=f from rfl,← hD,hi]; funext i U; exact Summable.tsum_add ((hp.summable U).comp_injective Subtype.val_injective) ((hl.summable U).comp_injective Subtype.val_injective)
    · have hi': (W).forced=M.forced+l:=hi
      funext U
      have hu': Summable u:= hs.2.1.of_nonneg_of_le (fun i=> (huP i).1) (fun i=> le_mul_of_one_le_left (huP i|>.1) (Real.one_le_exp (mul_nonneg (add_nonneg (R.p.exponent_pos.le) zero_le_two) (by positivity))))
      let t:=R.p.threshold
      let x0 (i:ℕ):=masked t (X i) (M.bulk i) U; let y0 (i:ℕ):=masked t (Y i) (M.bulk i) U
      have hfQ : Summable (fun i=> f i U):=hu'.of_norm_bounded (fun i=>(huP i).2 U)
      have hy : Summable y0:=hu'.of_norm_bounded (fun i=>by
         unfold y0; by_cases hY:Healthy t (Y i) U; rw [masked_eq _ _ _ _ hY]; exact (hU i).2 U (Finset.disjoint_of_subset_left (h.broad i) hY) [] (Nat.zero_le _) (by simp)
         rw [masked_ne _ _ _ _ hY,norm_zero]; exact (huP i).1)
      have ha : ∑' i,x0 i= (∑' i,y0 i)+∑' i,f i U:=by
         rw [← hy.tsum_add hfQ]; exact tsum_congr (fun i=> by unfold f update; rw [Pi.sub_apply]; change _=y0 i+(x0 i-y0 i); abel)
      have hz := ((Local.dominated_gasMark hu.packets hx.labels.boundK).summable U).hasSum.add (hK U)
      let b:Finset ℕ→ℂ:= fun s=> gasMark R.p R.activities U s q
      unfold Raw.eval; change (R.eval U:ℂ)*(Local.primary B o t M.seed U+ ∑' i,y0 i)+(Real.exp (R.exponent U):ℂ)*∑' i,b i= (R.eval U:ℂ)*(Local.primary B o t M.seed U+ ∑' i,x0 i)+ _
      have hA : ∑' i,b i=(∑' b',gasMark R.p R.activities U b' M.forced)+(∑' i,f i U)*(R.activities.gas R.p U:ℂ):=by
        refine Eq.trans (tsum_congr (fun i=> ?_)) hz.tsum_eq
        unfold b; rw [hi,map_add]
      rw [ha,hA]
      unfold Rep.eval; rw [Complex.ofReal_mul]; ring
    · rw [mul_add, show r*(ε*(g*a))= Ω*(g*a) by field_simp]; exact hu.packets.add hE
local notation "D" => Local.factor A B R.p.supportExponent e
local notation "ψ" => clipSum Y θ+coda B A o Y (out X M S) R
variable (S': Berths R.p R.activities (fun i=>joint B o (Y i)))
local notation "uG"=> mint S' (out X M S) A
include hr
lemma banner : let u:= mint S' (out X M S) A
     u.Format o A R ∧ u.density o B R=M.eval o X B R ∧ Tab u o R r (D*(g*a)) ((b+ε*(g*a))+ ε*(D*(g*a))) ∧ Attainment R.p o (clipSum Y θ+coda B A o Y (out X M S) R) (g*a+D*(g*a)) ∧ profile R.activities u.forced=profile R.activities M.forced+ hook R.activities R.p.threshold ψ:=by
   intro u; obtain ⟨hP,hF,hK,hB,hT⟩:=ledger (B:=B) X M S h hx hw hq hk hf hu
   have hh:= hT.tare hk hw hq hr hK; have hl:=vigor hT hK hr
   have hY:= attainAdd hP hl
   refine ⟨Guard.usage S' hK hx hr,(Guard.value_mint S' hK hx hk hr hh).trans hB, Guard.tab_mint S' hK hx hk hr hh,hY.1,?_⟩
   rw [show u=uG from rfl,hY.2]
   rw [← add_assoc,← hF]; exact budgetProfile S' hh hK hr hx hk
omit hu hk hq hw hx
lemma coordinate (T:Berths R.p R.activities (fun i=>joint B o (X i))) : (uG).x=(mint T M A).x:=by
   have hx i: Nonwrapping (X i) o ↔ Nonwrapping (Y i) o:=⟨h.thin i,fun ℓ a ha=> ℓ a (h.broad i ha)⟩
   let v:=R.p.threshold
   change M.seed+∑' i, weighted A F o (Y i) v (M.bulk i)= M.seed+∑' i, weighted A F o (X i) v (M.bulk i)
   apply congr_arg
   refine tsum_congr (fun i=> ?_)
   unfold weighted; congr 2; apply Push.Local.project_eq
   have he:=project_reads A o (hf.regular i) hr.order
   rw [Reads,hx] at he; exact he -- edit simp
end YM.LocalLTE.Dilation
