import YM.QuadraticLocal.Fingers
/-!
The complete marked re-expression on the input (= previous output). Pays the entire resource
for this Lyric call on true coupling, retains vacuum along with SAME slots *and*
forces all terms to follow their masks. Convergence of all series here is also needed even without
movement. No count assumptions on stimuli used in the algebra; count capacity is a criterion
only for supply rates through M.H.R.Cost.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Trigger
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open RG3 Progress.DirectedRecipe PhysicalNext PhysicalNext.Repeat Lotus Merge Palette
open RemainderComparison RemainderComparison.Lyric RemainderComparison.Muse RemainderComparison.Mosaic RemainderComparison.Serif RemainderComparison.Typeface
open GridRenewal.Rain
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge}{n c:Side}{P : Rep G n}{V:Type}[DecidableEq V]{R:Census V}{o:V→Site n}{a r r' s k b c' :ℝ}
variable {T:Type*}{I:Type}[Countable I] (A:Gallery T I o P R) (S:StepData c n)
set_option quotPrecheck false
local notation "p₀"=> P.p
local notation "X"=> P.activities
local notation "Fog0"=> Fog (fun i=>(P.activities.forced i).support) R o
local notation "J"=> Table A
local notation "J₁"=> J × Bool
variable (w:V→ℝ)
local notation "W"=> Poly.toll w
variable (hw:∀ i,0<w i) (hH:HasSlots P.p P.activities)
variable (g:I→ℝ)(d:ℕ→Poly R)
variable (hE:∀ i (t:T) (U:Config G n), ‖A.E.light t i U‖ ≤ g i)(hF:∀ i t U, Width.Covered (A.K.hard t i U) (d i))
local notation "φ"=> listCosts A w hw hH g d hE hF
local notation "Z"=> (Set.univ : Set J₁)
local notation "Λ"=> (fun _ : J₁=> (1:ℝ))
local notation "U₁"=> sits Z Λ 0
local notation "Vv"=> axis A w
variable (t:T)(U:Config G n)
local notation "Y" => brand φ t
local notation "P1"=> Encore.primitive Y U Z U₁ Vv
include hw
lemma colorCast (i:J₁) : P1 i= Poly.send (status A i.1) ((↑(slice i.2 (color A i.1 t U)):ℂ)*lens i.2) :=by
   unfold Encore.primitive Verse.controls; simp only [Multiset.map_singleton,Multiset.prod_singleton,Set.mem_univ,ite_true,sits, Verse.marked, Pi.mul_apply]
   rw [if_neg (fun h : i∈ Zᶜ=> h trivial),one_mul,one_mul]
   let b:= status A i.fst; let v:= W b; have h0:(v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Poly.worth hw b).ne'; unfold axis; ext q; rw [Poly.part_smul,Poly.part_send,Poly.part_send]; split_ifs; next h=>
       change ((↑(v*slice i.snd (color A i.fst t U)):ℂ)*((↑v⁻¹:ℂ)*_))=_; rw [Complex.ofReal_mul,Complex.ofReal_inv]; field_simp
   exact mul_zero _
lemma duet (i:J): ∑ j:Bool, P1 (i,j)=Poly.send (status A i) (color A i t U):=by
    ext q; rw [Poly.part_sum]; simp_rw [colorCast, Poly.part_send]; split_ifs with h; · simp [slice,lens,Complex.re_add_im,add_comm] -- Bool
    simp
variable {P':Pressure.Teller G} {o':ConnectedActivityE6.Target.Order G r'}{X':Pressure.Tube G S}{Q: ConnectedActivityE6.Target G P'} {L:Side}
variable (H:ConnectedActivityE6.Cash r' a r L Q o' k X' P)
variable {K k':ℕ} (hT:Motto (brand (listCosts A w hw hH g d hE hF) t) (fun _=>1) 0 H s b c' K)
variable (hC:Chorus R w (Set.univ : Set ((Table A) × Bool)) (axis A w) k')
include H hT hC
lemma summing : Summable P1:= (Poly.budgeted hC.votes (Encore.column Y U Z Λ Vv H hC hT) (fun _=>le_rfl)).1
lemma gasIdentity (i:ℕ): Encore.eatS (Encore.limb Y) P1 (Encore.Anc («J»:=R) (R:=P) U) i = A.K.hard t i U:=by
    let f(j:J₁):Poly R:= @ite _ (Encore.limb Y j= some i) (Classical.propDecidable _) (P1 j) 0; let D (i':J):Poly R:= i'.elim (fun _=>0) (fun j=> if j.val.fst=i then Poly.send j.val.snd (color A i' t U) else 0)
    have hs : Summable f:= by have ht : f = {j|Encore.limb Y j=some i}.indicator P1 := by exact funext fun j=> by by_cases hb:Encore.limb Y j=some i<;> simp [f, hb, Set.indicator];
                              exact ht.symm ▸ (summing A S w hw hH g d hE hF t U H hT hC).indicator {j| Encore.limb Y j= some i} -- def equality proof instances
    have he (j:J): ∑' b:Bool, f (j,b)= D j:=by
       rw [tsum_fintype]; cases j
       next j=> unfold D f; simp [Encore.limb,brand,listCosts,wing]
       next j =>
         unfold D f; simp only [Sum.elim_inr]; simp_rw [show ∀ b:Bool, Encore.limb Y (Sum.inr j,b)= some j.val.fst from fun _=> rfl, Option.some.injEq]; split; exact duet A w hw hH g d hE hF t U _; simp
    have hD : Summable D:= hs.prod.congr he
    have h1 := hD.comp_injective Sum.inr_injective
    refine (?_ : Encore.eatS (Encore.limb Y) P1 (Encore.Anc («J»:=R) (R:=P) U) i= Encore.Anc (R:=P) U i + ∑' i,f i).trans ?_
    · unfold Encore.eatS; refine congr_arg (_+·) (tsum_congr fun j=> ?_); unfold f; split <;> rfl
    let u(j:Fog0):Poly R:= D (.inr j)
    rw [hs.tsum_prod]; simp_rw [he]; rw [Summable.tsum_sum (f:=D) (hD.comp_injective Sum.inl_injective) (hD.comp_injective Sum.inr_injective)] -- check theorem
    let z:= A.K.hard t i U
    change _ +( (∑' j:Fires A,(0:Poly R))+∑' j:Fog0,u j)= z; rw [tsum_zero,zero_add]; ext q; rw [Poly.part_plus,Poly.share (show Summable u from h1)]
    let u' (j:ℕ×R.Mode) := ∀ j'∈ j.2.val,o j'∈ ((X).forced j.1).support
    have hz(q':R.Mode)(_h:q'≠R.quiet)(hj:¬ Origins (o:=o) ((X).forced i).support q'.val): z.part q'=0:= chop_carried A i t U q' hj -- syntax
    have hq (j:Fog0) {q:R.Mode}(he:j.val≠(i,q)): (u j).part q=0:= by
        unfold u D; rw [Sum.elim_inr]; split_ifs with ht
        · rw [Poly.part_send, if_neg (show q ≠ _ from fun H=>he (Prod.ext ht H.symm))]
        exact Poly.part_nil _
    unfold Encore.Anc; rw [Poly.part_smul,Poly.one_part]; split
    next H => subst q; rw [mul_one,tsum_congr (g:=fun _=>0) (fun j=> hq (q:=R.quiet) j (fun h=> j.property.1 (congr_arg Prod.snd h))), tsum_zero, add_zero]; exact (A.K.quiet ..).symm -- z def
    next ht=>
       rw [mul_zero,zero_add]; by_cases hh: u' (i,q)
       · let j:Fog0:=⟨(i,q),ht,hh⟩; rw [tsum_eq_single j (fun i hi=>hq i (fun hx=>hi (Subtype.ext hx)))]; unfold u D color; rw [Sum.elim_inr,if_pos (show j.val.1=i from rfl),Poly.part_send, if_pos (show q=j.val.2 from rfl), Sum.elim_inr]
       rw [hz q ht hh, tsum_congr (g:=fun _=>0) (fun j=> hq j (fun hx=>hh (hx ▸ j.property.2))),tsum_zero]
lemma prior_gas (i:Finset ℕ) : Encore.gas Y U Z U₁ Vv i= Fusion.Attached.packet P.activities P.p (A.K.hard t) U i:=by
    unfold Encore.gas Fusion.Attached.packet; split; simp_rw [gasIdentity A S w hw hH g d hE hF t U H hT hC]; rfl
variable [Fintype V]
omit [Fintype V] in
lemma layerSum : ∑' i,Encore.layer Y U Z Λ Vv (fun _ _=> 0) 0 i = ∑' i:Fires A,A.E.frame i.val t U:=by
    let F i:= Encore.layer Y U Z Λ Vv (fun _ _=> 0) 0 i
    let v:J→ Poly R:= Sum.elim (fun i=> Poly.send (status A (.inl i)) (color A (.inl i) t U)) (fun _=>0)
    have hh: F={j|Encore.limb Y j=none}.indicator P1:=by funext i; unfold F Encore.layer Set.indicator; by_cases hi:Encore.limb Y i=none<;> simp [hi]
    have he (i): ∑' b:Bool,F (i,b)=v i:=by
       rw [tsum_fintype]; cases i
       next i =>
          have h₁(j:Bool): F (Sum.inl i,j)= P1 (Sum.inl i,j):=by rw [hh,Set.indicator_of_mem]; exact (show Encore.limb Y (Sum.inl i,j)=none from rfl)
          simp_rw [h₁]; exact duet A w hw hH g d hE hF t U (.inl i)
       next i=> unfold F Encore.layer; simp_rw [show ∀ j:Bool,Encore.limb Y (Sum.inr i,j)=some i.val.fst from fun _=> rfl]; simp [v]
    have hs : Summable F:= hh.symm ▸ (summing A S w hw hH g d hE hF t U H hT hC).indicator {j| Encore.limb Y j=none}
    have hS:= hs.prod.congr he
    change (∑' i,F i)=_; rw [hs.tsum_prod]; simp_rw [he]; rw [Summable.tsum_sum (f:=v) (hS.comp_injective Sum.inl_injective) (hS.comp_injective Sum.inr_injective)]; change (∑' i:Fires A,A.E.frame i.val t U)+(∑' i:Fog0,(0:Poly R))=_; rw [tsum_zero,add_zero]
-- Portable global H. k marks above p-root stencil only. Keep exact summability.
def globes (t:T):Poly R:= ∑' i:{i// A.E.clear i},A.E.frame i.val t 1
omit hw H hT hC [Countable I] [Fintype V] in
lemma global (i:{i// A.E.clear i}): A.E.frame i.val t U=A.E.frame i.val t 1:=by
    unfold Lamps.frame Lamps.light; simp_rw [if_pos i.prop,A.E.pure t _ U i.prop]
variable {κ σ : ℝ} (hp:A.E.Paid w P.p.B κ σ)(hk:0≤κ)
include hp hk
omit [Fintype V] [Countable I] H hT hC in
lemma lensH : A.E.log t U= globes A t+ ∑' i:Fires A,A.E.frame i.val t U:= by
    simp_rw [Trigger.globes,← global A t U]; exact ((hp.sums hk hw t U).tsum_subtype_add_tsum_subtype_compl {i| A.E.clear i}).symm
lemma same : A.density t U= cyclone (globes A t)* TuneR Y Z Λ 0 Vv S U :=by
    unfold Gallery.density; rw [Encore.stamp Y U Z Λ Vv H hC hT (fun _ _=>0) (Encore.blueprint Y Λ (doors A w hw hH g d hE hF t) 0)] -- arg order
    rw [layerSum A S w hw hH g d hE hF t U H hT hC]; simp_rw [prior_gas A S w hw hH g d hE hF t U H hT hC]; rw [← GridRenewal.Rain.passes _ (Lamps.quiet_of_hasSum _ _ (hp.sums hk hw t U)), lensH A w hw t U hp hk,GridRenewal.Rain.plus]; rw [mul_assoc,mul_smul_comm]; rfl
end YM.QuadraticLocal.Trigger
