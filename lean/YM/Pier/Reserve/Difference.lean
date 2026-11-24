import YM.Pier.Reserve.Assembly
import YM.FullVolume.Mark.Booths
/-!
# Forced input gain survives the actual subtraction and projection

Keep the exact Ink transport. For two column stocks with *little regular*
difference and bounded forced difference, their actual differenced full single-mark
output `shot` profits from the small forced allowance. Prove it even with the
+2-ticket on regular output. No assumption on masks on configurations in
this norm. Do *not* cost `<volumewise density difference>` then try to change
it to a supported E/K norm. Adapted from Mark/Carts,Slate,Sight.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Pier.Slate
open MergeProof MergeProof.Matric
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
variable (P:Tool F H N p m){D:GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}{W:Worth}{T:Heading F}{c ε v t pE pK:ℝ}{X:Set Wing}
variable (hx:P.Cap B Y W D T c ε v X)(h:Well (H.rep N p (m+1)) S (Real.sqrt (H.levels.clock.forcedAllowance (m+1))))
open Extra.Histories.InputColumn
variable (i:F.Index)
local notation "J"=> Size.axis F i
local notation "u"=> tags P.plate P.up
variable (f g:Coin F Y S)
local notation "d₁"=> Matric.strip P i
local notation "d₂"=> gas P i
variable (hY : Lathe H N p m Y B (H.rep N p (m+1)) P.plate D c ε)
set_option quotPrecheck false
local notation "RotCost" => rotationBudget ((A₀).p)
include hx hY h

lemma toner (hf : Tab (book (Size.axis F i) (Coin.uses f)) 0 (A₁) (kappa H (m+1)) pE pK) : ∃ r:Listing→ℝ,SumBudget r (ε*(pE+μ'*pK)) ∧ ∀ j:Listing, Gate (tell (strip P i (Coin.uses f) j)) A₀ Y μ (r j) ∧
       Room (tell (strip P i (Coin.uses f) j)) 0 A₀ μ RotCost (r j) := by
    let A:= P.plate; let K:= P.up; let V:=book J (Coin.uses f); let Q:=rack P.up V; let w:= (H.rep N p (m+1)).p; let F₀:= P.plate; let S₁:=d₁ (Coin.uses f)
    obtain ⟨hc,hv⟩:= granted h Y J f
    have he:Q.Format 0 Y A₁:= rack_format P.up V hc; have hp:= capRack H N p m Y P.up hc hf
    obtain ⟨hμ,h₁,h₂,⟨E,hE,hM⟩,q,hq,hQ⟩:= hp
    let e(i:ℕ):=w.mass (V.support i) (E i); let k(i:ℕ):= w.mass ((H.rep N p (m+1)).activities.forced i).support (q i)
    have hg := hx.budget.epsilon; have hR:SumBudget k (μ'*pK) := hq
    let r:Listing→ℝ:= consist 0 (fun i=> ε*e i) (fun i=> ε*k i)
    have hr:HasSum r (0+ε*((∑' i,e i)+∑' i,k i)):= by rw [mul_add]; exact added ((show Summable e from hE.2.1).hasSum.mul_left ε) (hR.2.1.hasSum.mul_left ε)
    have hi {j:Listing}(he:S₁ j=0)(h:0≤r j):Gate (tell (strip P i (Coin.uses f) j)) A₀ Y μ (r j) ∧
       Room (tell (strip P i (Coin.uses f) j)) 0 A₀ μ RotCost (r j) := by
       have h' : strip P i (Coin.uses f) j=0:=he; rw [h']
       have hp:= (spanNone B H N p m Y X D (t:=r j) h (le_refl (0:ℝ))).earns; have hp':=hp.leadP; rw [sub_zero] at hp'; exact ⟨⟨hp',hp.format,hp.future⟩,Room.blank (Real.sqrt_pos.mpr (forcedPos ..)) h⟩
    have hv(j:Listing): Gate (tell (strip P i (Coin.uses f) j)) A₀ Y μ (r j) ∧
       Room (tell (strip P i (Coin.uses f) j)) 0 A₀ μ RotCost (r j) := by
       rcases j with i|i|j
       · exact hi rfl le_rfl
       · have hu:= (hx.copies.regular i (Q.regular i) (E i) ⟨he.smooth _, he.origin _, he.identity_null _,he.projects _⟩ (hM i)).earns
         have he' := hu.leadP; rw [sub_zero] at he'; exact ⟨⟨he',hu.format,hu.future⟩,
           hY.regular i _ _ ⟨he.smooth _, he.origin _, he.identity_null _,he.projects _⟩ (hM i)⟩
       · by_cases H₀ : Q.forced j=0
         · exact hi (j:=.inr (.inr j)) (show P.plate.ink j (Q.forced j)=0 from (congr_arg (P.plate.ink j) H₀).trans (hx.copies.blank j)) (mul_nonneg hg (hR.1 j))
         have H' : X (.gasKey j) :=by
            have hd: j∈ Set.range (cart K):= not_not.mp (fun h=> H₀ (pit K V h)); obtain ⟨j,rfl⟩:=hd; exact hx.cart _
         have hu:= (hY.forced j (Q.forced j) (q j) X H' H₀ ⟨he.invariant _,he.borel _,he.supported _,he.carried _,he.forcing _⟩ (hQ j).2)
         have he' := hu.2.earns.leadP; rw [sub_zero] at he'; exact ⟨⟨he',hu.2.earns.format,hu.2.earns.future⟩,hu.1⟩
    refine ⟨r,⟨fun i=>rem_nonneg (hv i).1.rem, hr.summable,?_⟩,hv⟩
    rw [hr.tsum_eq, zero_add]; exact mul_le_mul_of_nonneg_left ((add_le_add hE.2.2 hR.2.2).trans le_rfl) hg


theorem recoilDelta (ha:Afford P.plate Y (H.rep N p (m+1)) (H.rep N p m))
    (hf : Tab (book (Size.axis F i) (Coin.uses (f-g))) 0 A₁ (kappa H (m+1)) pE pK) :
    Gate (breakP (P.shot i (Coin.uses f)) (P.shot i (Coin.uses g))) A₀ Y μ (ε*(pE+μ'*pK)) ∧
    Room (breakP (P.shot i (Coin.uses f)) (P.shot i (Coin.uses g))) 0 A₀ μ (rotationBudget ((A₀).p)) (ε*(pE+μ'*pK)) := by
    obtain ⟨r,hp,he⟩:= toner P hx h i (f-g) hY hf; obtain ⟨hv,hq⟩:= solace P hx h i f; obtain ⟨hV,hQ⟩:= solace P hx h i g
    let Z' j:=gas P i (Coin.uses f) j- gas P i (Coin.uses g) j; let Y' j:= tell (Z' j)
    have g'(j):Gate (Y' j) (A₀) Y μ (r j) ∧
         Room (Y' j) 0 A₀ μ (rotationBudget ((A₀).p)) (r j) := by
       let X':=turnCost
       let E j:= strip P i (Coin.uses (f-g)) j
       obtain ⟨hV,hQ⟩:= travels P hx h i f g ha j
       obtain ⟨a,b,Hv,⟨bill,hZ,hθ'⟩,hθ⟩:= (he j).2
       have hz:(Y' j).x = (tell (E j)).x:= hQ.point
       obtain ⟨A,hA,hX⟩:=Hv.regular
       have hv : Tab (Y' j) 0 A₀ μ a b :=
         ⟨Hv.divisor,Hv.first,Hv.second,⟨_, hA,fun i=>hQ.germs i _ _ (hX i) le_rfl⟩,by
           rw [show (Y' j).forced= (tell (E j)).forced from hQ.force]; exact Hv.forced⟩
       exact ⟨⟨(hz.symm ▸ (he j).1.first: _),hV,a,b,hv,hθ⟩, a,b,hv,⟨_,hZ,fun i=>hQ.germs i _ _ (hθ' i) le_rfl⟩,hθ⟩
    have hh : Extra.Histories.merge (code _) Y'= breakP (P.shot i (Coin.uses f)) (P.shot i (Coin.uses g)):=by unfold Y' Z'; simp_rw [tell_br]; exact melt _ hv hV hq hQ -- hx
    rw [← hh]; exact ⟨(Gate.together (Real.sqrt_pos.mpr (forcedPos H.levels m)) _ hp.2.1 (fun j=>(g' j).1) (code _)).weaker hp.2.2, (Room.combine (code Listing) (rotationBudget_one _) (Real.sqrt_pos.mpr (forcedPos ..)) (fun j=>(g' j).2) hp.2.1).larger hp.2.2⟩
end YM.Pier.Slate

namespace YM.Pier.Slate
open MergeProof MergeProof.Matric
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{B:SectionData F}{H:History G} {N p m:ℕ} {Y:Hol G}

/-! In the comparison of the assembled full single-mark columns against
changed stocks we will likewise use an evaluator (`breakP`). Verify
that this delta at the level of the actual supported files IS the one
used to read both densities, all configurations (common `p` and price).
No term `dressed` is repointed by this lemma. -/
section diff
variable {n : Side} {R:Rep G n} {o:Site n}
    {X Y:Coefficient F n} {a b c t σ M V u v : ℝ}
    (hk:R.Lawful σ M V u v) (hu:X.remBound o R t a)
    (hv:Y.remBound o R t b) (h:(breakP X Y).remBound o R t c) (hs:X.support=Y.support)

include hu hv hs

lemma exponential_difference :
    (breakP X Y).exponentialEntry o B R=X.exponentialEntry o B R-Y.exponentialEntry o B R := by
  funext U
  let l Z := part B o R U Z
  have hx(Z:Coefficient F n) : Z.exponentialEntry o B R U=l Z.x+∑' i,Z.maskedTerm R i U:=rfl
  have hm i : (breakP X Y).maskedTerm R i U = X.maskedTerm R i U - Y.maskedTerm R i U := by
    unfold Coefficient.maskedTerm
    rw [show (breakP X Y).support=X.support from rfl, hs]
    exact congr_fun (map_sub (Local.maskLinear R.p.threshold (Y.support i)) (X.regular i) (Y.regular i)) _
  rw [hx,Pi.sub_apply,hx,hx]
  simp_rw [hm,(X.regular_series hu|>.summable U).tsum_sub (Y.regular_series hv|>.summable U),
    show l (breakP X Y).x= l X.x-l Y.x from map_sub (part B o R U) X.x Y.x]
  ring

include hk h
lemma density_difference :
    (breakP X Y).density o B R=X.density o B R-Y.density o B R := by
  have hz (Z:Coefficient F n) (hu : Dominated Z.forced) (U) :
      Z.density o B R U= R.eval U * Z.exponentialEntry o B R U +
        ↑(Real.exp (R.exponent U))*(∑' i, Z.forced i U * dressed R i U) := by
    unfold Coefficient.density; rw [dress_eq hk hu]
  funext U
  rw [hz _ (rem_dominated h),Pi.sub_apply,hz _ (rem_dominated hu),hz _ (rem_dominated hv),exponential_difference (B:=B) hu hv hs, Pi.sub_apply]
  simp_rw [fun i => show (breakP X Y).forced i U * dressed R i U =
    X.forced i U * dressed R i U - Y.forced i U * dressed R i U from sub_mul ..,
    (dress_abs hk (rem_dominated hu)|>.summable U).tsum_sub (dress_abs hk (rem_dominated hv)|>.summable U)]
  ring
end diff

end YM.Pier.Slate
