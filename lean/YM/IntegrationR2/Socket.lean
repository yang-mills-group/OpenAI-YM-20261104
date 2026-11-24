import YM.FullVolume.Mark.Sight
import YM.IntegrationR2.Assemble
/- Building on / adapting the FullVolume.Mark.Sight tram/socket proofs, but strengthening the Lipschitz constant in the forced sector and exporting +2 regular reserve. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric.R2
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{B:SectionData F}{H:History G} {N p m:ℕ} {Y:Hol G}
local notation "A₀"=>H.rep N p m
local notation "A₁"=>H.rep N p (m+1)
local notation "s₀"=> H.S.side (m+1) p
local notation "s₁"=> H.S.side m p
local notation "Z"=> orbitCost F
local notation "μ"=>kappa H m
local notation "μ'"=> Real.sqrt (H.levels.clock.forcedAllowance (m+1))
variable {S:Desk G (H.S.side (m+1) p)}
variable (P:Tool F H N p m){D:GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}{W:Worth}{T:Heading F}{c ε v t:ℝ}{X:Set Wing}
variable (hx:P.Cap B Y W D T c ε v X)(h:Well (H.rep N p (m+1)) S (Real.sqrt (H.levels.clock.forcedAllowance (m+1))))
open Extra.Histories.InputColumn
variable (i:F.Index)
local notation "J"=> Size.axis F i
local notation "u"=> tags P.plate P.up
variable (f g:Coin F Y S)
local notation "d₁"=> Matric.strip P i
variable (Hplus:ReservePlate B H N p m Y (H.rep N p (m+1)) (H.S.block m) P.plate c ε D)
include hx h Hplus
omit h in
set_option maxHeartbeats 800000 in
lemma plusMap (u₀:File G (H.S.side (m+1) p))(hU:(book (Size.axis F i) u₀).Format 0 Y A₁) {a b:ℝ} (hV: Tab (book J u₀) 0 A₁ μ' a b) : ∃ r:Listing→ℝ,SumBudget r (ε*(a+ μ' *b)) ∧ ∀ j:Listing, Gate (tell (strip P i u₀ j)) A₀ Y μ (r j) ∧ Plus A₀ (tell (strip P i u₀ j)) (r j) :=by
    let A:= P.plate; let K:= P.up; let V:=book J u₀; let Q:=rack P.up V; let w:= (H.rep N p (m+1)).p; let F₀:= P.plate; let S₁:=d₁ u₀
    have hc:=hU
    have he:Q.Format 0 Y A₁:= rack_format P.up V hc; have hp:= keeps P.up V (hV.bound le_rfl)
    have htab : Tab Q 0 (A₁) (μ') a b := rack_reserve P.up hc hV
    obtain ⟨E,hE,hM⟩:= htab.regular; obtain ⟨q,hq,hQ⟩:= htab.forced
    let e(i:ℕ):=w.mass (V.support i) (E i); let k(i:ℕ):= w.mass ((H.rep N p (m+1)).activities.forced i).support (q i)
    have hg := hx.budget.epsilon
    let r:Listing→ℝ:= consist 0 (fun i=> ε*e i) (fun i=> ε*k i)
    have hr:HasSum r (0+ε*((∑' i,e i)+∑' i,k i)):= by rw [mul_add]; exact added ((show Summable e from hE.2.1).hasSum.mul_left ε) (hq.2.1.hasSum.mul_left ε)
    have hi {j:Listing}(he:S₁ j=0)(h:0≤r j):Gate (tell (strip P i u₀ j)) A₀ Y μ (r j) ∧ Plus A₀ (tell (strip P i u₀ j)) (r j) :=by
       have h' : strip P i u₀ j=0:=he; rw [h']
       have hp:= (spanNone B H N p m Y X D (t:=r j) h (le_refl (0:ℝ))).earns; have hp':=hp.leadP; rw [sub_zero] at hp'; exact ⟨⟨hp',hp.format,hp.future⟩,Plus.nil h⟩
    have hv(j:Listing): Gate (tell (strip P i u₀ j)) A₀ Y μ (r j) ∧ Plus A₀ (tell (strip P i u₀ j)) (r j) :=by
       rcases j with i|i|j
       · exact hi rfl le_rfl
       · have hu:= (hx.copies.regular i (Q.regular i) (E i) ⟨he.smooth i, he.origin i, he.identity_null i,he.projects i⟩ (hM i)).earns
         have he' := hu.leadP; rw [sub_zero] at he'; exact ⟨⟨he',hu.format,hu.future⟩, Hplus.regular i (Q.regular i) (E i) ⟨he.smooth i, he.origin i, he.identity_null i,he.projects i⟩ (hM i)⟩
       · by_cases H₀ : Q.forced j=0
         · exact hi (j:=.inr (.inr j)) (show P.plate.ink j (Q.forced j)=0 from (congr_arg (P.plate.ink j) H₀).trans (hx.copies.blank j)) (mul_nonneg hg (hq.1 j))
         have H' : X (.gasKey j) :=by
            have hd: j∈ Set.range (cart K):= not_not.mp (fun h=> H₀ (pit K V h)); obtain ⟨j,rfl⟩:=hd; exact hx.cart _
         have hj : SlotFit (A₁) 0 j (Q.forced j) := ⟨he.invariant j,he.borel j,he.supported j,he.carried j,he.forcing j⟩
         have hl : ∀ U, ‖Q.forced j U‖ ≤ q j := (hQ j).2
         have hu:= (Hplus.forced X j (Q.forced j) (q j) H₀ H' hj hl)
         have hF:= hu.1.earns; have he' := hF.leadP; rw [sub_zero] at he'; exact ⟨⟨he',hF.format,hF.future⟩,hu.2⟩
    refine ⟨r,⟨fun i=>rem_nonneg (hv i).1.rem, hr.summable,?_⟩,hv⟩
    rw [hr.tsum_eq, zero_add]; exact mul_le_mul_of_nonneg_left (add_le_add hE.2.2 hq.2.2) hg
lemma socketPlus (ha:Afford P.plate Y (H.rep N p (m+1)) (H.rep N p m)) {a b:ℝ}(ht:Tab (book J (Coin.uses (f-g))) 0 A₁ μ' a b) : Gate (breakP (P.shot i (Coin.uses f)) (P.shot i (Coin.uses g))) A₀ Y μ (ε*(a+ μ' *b)) ∧ Plus A₀ (breakP (P.shot i (Coin.uses f)) (P.shot i (Coin.uses g))) (ε*(a+ μ' *b)):=by
    obtain ⟨r,hp,he⟩:= plusMap P hx i Hplus (Coin.uses (f-g)) (granted h Y J (f-g)).1 ht; obtain ⟨hv,hq⟩:= solace P hx h i f; obtain ⟨hV,hQ⟩:= solace P hx h i g
    let Z' j:=gas P i (Coin.uses f) j- gas P i (Coin.uses g) j; let Y' j:= tell (Z' j)
    have g'(j):Gate (Y' j) (A₀) Y μ (r j) ∧ Plus A₀ (Y' j) (r j):=by
       let X':=turnCost
       let E j:= strip P i (Coin.uses (f-g)) j
       obtain ⟨hV,hQ⟩:= travels P hx h i f g ha j
       obtain ⟨a,b,Hv,hθ⟩:= (he j).1.income
       have hz:(Y' j).x = (tell (E j)).x:= hQ.point
       obtain ⟨A,hA,hX⟩:=Hv.regular
       have hG : (Y' j).forced=(tell (E j)).forced:=hQ.force
       -- Pros supplies the full derivative bound of the difference on the
       -- same E support. K subtraction still aligns exactly.
       constructor
       · refine ⟨(hz.symm ▸ (he j).1.first: _), hV,a,b,⟨Hv.divisor,Hv.first,Hv.second,⟨_, hA,fun i=>hQ.germs i _ _ (hX i) le_rfl⟩,?_⟩,hθ⟩
         rw [hG]; exact Hv.forced
       obtain ⟨e,h',hx⟩:= (he j).2
       exact ⟨_,h',fun i=> hQ.germs i _ _ (hx i) le_rfl⟩
    have hh : Extra.Histories.merge (code _) Y'= breakP (P.shot i (Coin.uses f)) (P.shot i (Coin.uses g)):=by unfold Y' Z'; simp_rw [tell_br]; exact melt _ hv hV hq hQ -- hx
    rw [← hh]; exact ⟨(Gate.together (Real.sqrt_pos.mpr (forcedPos H.levels m)) _ hp.2.1 (fun j=>(g' j).1) (code _)).weaker hp.2.2,(Plus.joins (code _) (fun j=>(g' j).2) hp.2.1).more hp.2.2⟩
end YM.MergeProof.Matric.R2

