import YM.QuadraticLocal.Tint.Clash
import YM.QuadraticLocal.Earn.Blend
import YM.QuadraticLocal.Travel
/-!
 # Name space for heterogeneous tickets at the *real representation*

 Step always buys HUGE support invariant collars & queries per ACTUAL polynomial.
 Competitors here split only by their locations the owner registry. `Candidate` MUST authenticate
 via actual addresses—not choose equivalent Ψ representation in enlarged frame; only extension
 symbols used inside campus. Require assignment before test parameter/palette input. Use [α]
 ambient holder space independent product.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Tint
open Function Filter Finset Lattice RG Wilson Marker Ac Push Push.AbsoluteSums Paths Animals
open QuadraticLocal.Sunrise QuadraticLocal.Earn AllOrder AllOrder.Ink
open Push.SectorMeasure ConnectedActivityE6 RemainderComparison Trigger
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V α ι J: Type}[DecidableEq V]{G:Gauge}{n c:Side}
variable {P:Passport n V} {R:Census V} {g a e r b :ℝ} {k i' j u i h : ℕ}
variable (X:ι→Row P R G α) (C:Club X)
open Travel Club Typeface Lyric
structure Incoming (P:Passport n V)(U:RG.Rep G n)(α η:Type)(R:Marker.Census V) where
   old : Lamps α η G U.p P.origin R
   hard : Hard α U.p U.activities.forced U.activities.K P.origin R
variable {U:RG.Rep G n} (T:Incoming P U α J R) (w:V→ℝ)(hw:∀ i,0<w i)
set_option quotPrecheck false
namespace Patrol
local notation "YR"=> Coat.gStep U.beta

def picture : QuadraticLocal.Gallery α (ι⊕J) P.origin U R:= ⟨(rendered X U.p (YR)).join T.old,T.hard⟩
local notation "Z₀"=> Patrol.picture X T
-- Names : COUNTABLE at enrollment, transport all along Realm. C.Index assembly strongly.
abbrev Shift := Trigger.Table (Patrol.picture X T) × Bool
def enter (i : {i:ι// ¬ (X i).clear} × Bool): Shift X T:= (Sum.inl (⟨Sum.inl i.fst.val,i.fst.prop⟩: Fires Z₀),i.snd)
private def ent (i : {i:J// ¬T.old.clear i} × Bool): Shift X T:= (Sum.inl (⟨Sum.inr i.fst.val,i.fst.prop⟩: Fires Z₀),i.snd)
local notation "L₀"=> (Shift X T)
local notation "K"=> Club.Keys X C
local notation "δ"=> (Club.ticket X C)
local notation "Φ"=> (Club.stamp X C)
abbrev Signs := Club.Keys X C→ Bool
variable (σ:Signs X C)
abbrev ticketA (i:Club.Keys X C) : {i:ι // ¬ (X i).clear}:= ⟨Club.stamp X C i,Club.all_masked X C (Club.stamp X C i) (Club.attends ..)⟩
abbrev out (i: Club.Keys X C) : Shift X T := Patrol.enter X T (Patrol.ticketA X C i,σ i)
local notation "f₀"=> (Patrol.out X C T σ)
lemma receives : Injective (Patrol.enter X T):= by
    rintro ⟨i,x⟩ ⟨j,y⟩ h; obtain ⟨h,rfl⟩:= Prod.mk.inj h;
    exact Prod.ext (Subtype.ext (Sum.inl_injective (congr_arg Subtype.val (Sum.inl_injective h)))) rfl
lemma enroll : Injective (Patrol.out X C T σ):= fun i j h=> Club.troop_inj X C (congr_arg (fun i=> i.val) (congr_arg Prod.fst ((receives X T) h)))
def pulp : Finset (Shift X T) := Finset.univ.image (Patrol.out X C T σ)
local notation "P₁"=> (Patrol.pulp X C T σ)
lemma present (i:K) : f₀ i∈ P₁:= mem_image_of_mem _ (mem_univ i)
lemma courseCard : (P₁).card=C.val.card:= (Finset.card_image_of_injective _ (enroll ..)).trans ((card_univ).trans (Fintype.card_fin _))
lemma member (i:L₀): i∈P₁ ↔ ∃ j:Club.Keys X C,f₀ j=i:= by unfold Patrol.pulp; simp
lemma naming (p:Shift X T) : p=p := rfl -- clean later
-- joint stake on Campus(C)*Sign. λ carrying.
def seminar : (Σ y: Club X, Patrol.Signs X y) ↪ Finset (Shift X T):= by
    refine ⟨(fun i=> Patrol.pulp X i.1 T i.snd),?_⟩; rintro ⟨i,b⟩ ⟨j,f⟩ hk
    have he(i j:Club X)(b: Club.Keys X i→Bool) (f:Club.Keys X j→Bool) (h:Patrol.pulp X i T b⊆ Patrol.pulp X j T f)(k:Club.Keys X i): ∃ k':Club.Keys X j,Club.stamp X j k'=Club.stamp X i k ∧ b k=f k':=by
       obtain ⟨l,hl⟩:= (Patrol.member ..).1 (h (Patrol.present X i T b k)); have ht:= Prod.mk.inj ((receives X T) hl); exact ⟨l,congr_arg Subtype.val ht.1,ht.2.symm⟩
    have ht(i j:Club X)(b f)(h:Patrol.pulp X i T b⊆Patrol.pulp X j T f):i.val⊆ j.val:=by intro p hp; obtain ⟨k,rfl⟩:= Club.attends_rev _ _ _ hp; obtain ⟨l,hl,-⟩:= he _ _ _ _ h k; rw [← hl]; exact Club.attends ..
    change Patrol.pulp X i T b=Patrol.pulp X j T f at hk; have h:i=j:= Subtype.ext (Finset.Subset.antisymm (ht _ _ _ _ hk.subset) (ht _ _ _ _ hk.symm.subset)); subst j; refine Sigma.ext rfl (heq_of_eq ?_); ext1 x; obtain ⟨z,hz,hm⟩:= he _ _ b f hk.subset x; change b x = f x; rw [hm, Club.troop_inj X i hz];

abbrev stakeholder (i:Shift X T): R.Mode:= Trigger.status (Patrol.picture X T) i.1
abbrev way (i:Shift X T):= (↑((Poly.toll w (stakeholder X T i))⁻¹):ℂ) * Trigger.lens i.snd
theorem join_pair : Clash.apart (Patrol.stakeholder X T) (P₁) ∧ (Clash.issued (Patrol.stakeholder X T) (P₁)=(Club.alliance X C).val):=by
    let u i:=(stakeholder X T i); constructor
    · intro i hi j hj he; obtain ⟨i,rfl⟩:= (member ..).1 hi; obtain ⟨j,rfl⟩:= (member ..).1 hj; exact Club.apart X C (Club.attends X C i) (Club.attends X C j) ((Club.troop_inj X C).ne (fun h=> he (congr_arg f₀ h))) -- type f₀?
    rw [Club.cites]; unfold Clash.issued; ext1 x; constructor
    · intro hi; obtain ⟨i,hi',hh⟩:= Finset.mem_biUnion.mp hi; obtain ⟨y,rfl⟩:= (Patrol.member ..).1 hi'; exact Finset.mem_biUnion.mpr ⟨y,mem_univ _,hh⟩
    intro hi; obtain ⟨i,_,h⟩:= Finset.mem_biUnion.mp hi; exact Finset.mem_biUnion.mpr ⟨_,present X C T σ i,h⟩
-- TRUE kernel funding with λ',ρ. All phases.
def photon :ℂ:= ∏ i:Club.Keys X C, Trigger.lens (σ i)
lemma photon_ok : ‖photon X C σ‖=1:=by unfold photon; rw [norm_prod]; simp_rw [Trigger.tone_size]; simp
local notation "η"=> Club.alliance X C
local notation "Y"=> Poly.toll w (Club.alliance X C)
def price :ℂ:= (Y:ℂ)⁻¹ * photon X C σ
local notation "E"=> Clash.beacon (stakeholder X T) (way X T w) (Patrol.pulp X C T σ)
lemma fortune : (E)=Poly.send (Club.alliance X C) (price X C w σ) :=by
    obtain ⟨h₁,h₂⟩:=join_pair X C T σ; rw [Clash.glows _ _ _ h₁ h₂]; apply congr_arg; unfold price Patrol.pulp; rw [Finset.prod_image (enroll X C T σ).injOn]; change (∏ i:Club.Keys X C, (↑( (Poly.toll w (X (Φ i)).mode)⁻¹):ℂ)* Trigger.lens (σ i))= _; rw [Finset.prod_mul_distrib]; congr 1; simp_rw [Complex.ofReal_inv]; rw [Club.union_price, Finset.prod_inv_distrib, Club.product X C (fun i=>(↑(Poly.toll w (X i).mode):ℂ)), Complex.ofReal_prod]
include hw in
lemma worth : Y*‖price X C w σ‖=1:= by rw [price,norm_mul,photon_ok,mul_one,norm_inv, Complex.norm_real,Real.norm_of_nonneg (Poly.worth hw _).le, mul_inv_cancel₀ (Poly.worth hw _).ne']
include hw
lemma qualifies : Clash.lit (stakeholder X T) (way X T w) (Patrol.pulp X C T σ):= by
   let u:= Club.lowest X C; have h:= worth X C w hw σ; have ht:(price X C w σ)≠0:= by intro hn; rw [hn,norm_zero,mul_zero] at h; norm_num at h
   refine ⟨η,?_ , ?_⟩
   · let v₀:=Club.troops X C u; intro h; have h' : v₀.binder.front∈ (η).val:= Club.earn X C (Φ u) (Club.attends ..) ((X (Φ u)).binder.east); rw [h] at h'; exact Finset.notMem_empty _ h'
   rw [fortune,Poly.part_send,if_pos rfl]; exact ht
end Patrol
end YM.QuadraticLocal.Tint
