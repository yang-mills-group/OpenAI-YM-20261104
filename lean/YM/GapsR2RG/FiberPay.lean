import YM.GapsR2RG.TranslateCov
/-!
 Assemble uncentered regular AND forced affine-null pieces at the true linearization point with zero x. Not assuming a budget on the output. At each step divide by L^4 on true density before summing parent fibers. Adapt the `Histories.InputColumn.individual` sum and Sonatas' merging *after* strengthening current Graces at noncentered sites.
-/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 30000
set_option quotPrecheck false
noncomputable section
namespace YM.GapsR2RG
open Lattice Wilson RG Source Labels Function Filter Set MeasureTheory Finset Push.Local Extra.Histories Planned.GuardedAtom
open Bid
open scoped Classical Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G:Gauge}{n:Side}
namespace Anchor
open MergeProof PhysicalNext.Repeat.Legato Next.Foundations
variable {d:ℕ}
local notation "F" => (Labels.frames G).level d
variable (hG:G.Simple)(R:Run G){N p m:ℕ}(hm:m<N)(hl:R.t d ≤ m)
local notation "H" => R.family.path
local notation "V" i => R.family.side i p
local notation "Q" i => (H).rep N p i
local notation "e" => Doors.rate ((H).S.block m)
local notation "L" => ((H).S.block m)
local notation "R'" => Q (m+1)
local notation "κ" i => (kappa H i)
local notation "J" => (localSection G d)
private lemma dominated_mul {W : Type*} {u : W → ℂ} {f : ℕ → W → ℂ} (h : Dominated f) (hv : ∃ c : ℝ, ∀ x, ‖u x‖ ≤ c) :
    Dominated fun i x => u x * f i x := by
  obtain ⟨b,hb,hr⟩ := h; obtain ⟨c,hh⟩ := hv
  exact ⟨_,hb.mul_left c,fun i x => (norm_mul ..).trans_le <| mul_le_mul (hh x) (hr ..) (norm_nonneg _) ((norm_nonneg _).trans (hh x))⟩
include hG R hm hl
lemma centralFiber (y:Site (R.family.side (m+1) p))(hy: ((H).levels.clock.op m p).ratio.parent y=0)(P: Coefficient F (V (m+1)))(hx:P.x=0) (t:ℝ)(h:P.Format y (hol G) R')(hq:P.remBound y R' (κ (m+1)) t): ∃ U: Coefficient F (V m),
    U.Format 0 (hol G) (Q m) ∧ U.density 0 J (Q m) = blast H N p m d (P.density y J R') ∧ U.remBound 0 (Q m) (κ m) (e*t) ∧ (F).coeffSize U.x ≤ e*t :=by
   have hW:= hq
   obtain ⟨c,u,ha,hb,hS,-,⟨a,hA,hA'⟩,b,hB,hB'⟩ := hq
   let Y:= κ (m+1); have h0:0<Y:=Real.sqrt_pos.2 (forcedPos ..)
   let CostReg i := (R').p.mass (P.support i) (a i)
   let CostK i := (R').p.mass ((R').activities.forced i).support (b i)/Y
   let V0:= Sum.elim (fun i=> e*CostReg i) (fun i=>e*CostK i)
   have Hg : HasSum CostReg (∑' i, CostReg i) := hA.2.1.hasSum
   have Hk : HasSum CostK (∑' i, CostK i) := (hB.2.1.div_const Y).hasSum
   have he := (Hg.mul_left e)|>.sum (Hk.mul_left e) (f:=V0)
   have hSmall : ∑' i,V0 i ≤ e*t:=by
     rw [he.tsum_eq,←mul_add]; apply mul_le_mul_of_nonneg_left (le_trans (add_le_add hA.2.2 ?_) hS) (Doors.rate_pos _|>.le)
     unfold CostK; rw [tsum_div_const]; exact (div_le_iff₀ h0).mpr (hB.2.2.trans_eq (mul_comm ..))
   let f: (ℕ ⊕ ℕ) → Config G (R.family.side (m+1) p)→ ℂ:= Sum.elim (fun i => salary R' (P.support i) (P.regular i)) (fun i => fare R' i (P.forced i))
   have hk:= R.makes.wilson; have hGood:= (hk.represents N p (m+1) hm).good
   have hE := Rep.envelope (Q (m+1)) hGood
   have hR := (Rep.exponentEnv (Q (m+1)) hGood).exp
   have hL := rem_dominated hW
   have hu : Dominated f := by
     obtain ⟨M,hM,hM'⟩:= dominated_mul (P.regular_series hW) (u:=fun i=>((Q (m+1)).eval i:ℂ)) (by obtain ⟨c,hc⟩ := hE.cost; exact ⟨c, fun i => (Complex.norm_real _).trans_le (hc i)⟩)
     obtain ⟨W,hT,hT'⟩:= dominated_mul (dress_abs hGood hL) (u:=fun i=>(Real.exp ((Q (m+1)).exponent i) :ℂ)) (by obtain ⟨c,hc⟩ := hR.cost; exact ⟨c, fun i => (Complex.norm_real _).trans_le (hc i)⟩)
     exact ⟨Sum.elim M W,HasSum.sum (f:=Sum.elim M W) (hM.hasSum) (show HasSum (_ ∘ Sum.inr) (∑' i,W i) from hT.hasSum)|>.summable,fun s=>by rcases s with i|i; exact fun z=> hM' i z; exact fun z=> hT' i z⟩
   have hf (i : ℕ ⊕ℕ) : Measurable (f i) := by
    rcases i with i|i
    · exact (Complex.continuous_ofReal.measurable.comp hE.meas).mul (masked_measurable _ _ _ (h.smooth i).borel)
    exact (Complex.continuous_ofReal.measurable.comp hR.meas).mul ((h.borel i).mul (dressed_meas hGood i))
   have hv : P.density y J R' = fun U => ∑' i, f i U := by
    funext U
    let a' i := P.maskedTerm R' i U; let b' i := P.forced i U * dressed R' i U
    have hm : HasSum a' (∑' i, a' i) := ((P.regular_series hW).summable U).hasSum
    have hn : HasSum b' (∑' i, b' i) := ((dress_abs hGood hL).summable U).hasSum
    rw [(HasSum.sum (f:=fun i=> f i U) (hm.mul_left ((R').eval U:ℂ)) (hn.mul_left (Real.exp ((R').exponent U):ℂ))).tsum_eq]
    rw [Coefficient.density,dress_eq (R:=R.family.path.rep N p (m+1)) hGood hL]
    change ((R').eval U:ℂ)*(part J y R' U P.x+∑' i,a' i) + _ = _
    rw [hx,map_zero]; simp [b']
   obtain ⟨hC,hK⟩:=fibers hG R hm hl y hy
   have ht (j : ℕ ⊕ℕ) : ∃ U, Gig J H N p m (hol G) (f j) U 0 (V0 j) (V0 j) := by
     rcases j with j|j
     · exact hC _ _ _ ⟨h.smooth j,h.origin j,h.identity_null j,h.projects j⟩ (hA' j)
     exact hK _ _ _ ⟨h.invariant j,h.borel j,h.supported j,h.carried j,h.forcing j⟩ (hB' j).1 (hB' j).2
   choose Z hZ using ht
   have hResult:= Gig.all_in J H N p m (hol G) hk hm.le hZ hu hf (by simp [Frame.coeffSize]) he.summable he.summable
   let U:=Extra.Histories.merge (code _) Z
   change Gig .. at hResult
   rw [←hv,tsum_zero] at hResult; have hs:= hResult.weaken hSmall hSmall
   exact ⟨U,hs.format,hs.agrees,hs.bound,(le_mul_of_one_le_left (Work.G08.size_nonneg ..) (Motion.orbitCost_one_le F)).trans (sub_zero U.x ▸ hs.leadP)⟩
open Motion
local notation "Ratio'" => ((H).levels.clock.op m p).ratio
private lemma parentRebase (y:Site _) : (Ratio').parent (y - (Ratio').embed ((Ratio').parent y))= 0 :=by
    generalize hq : (Ratio')=r
    obtain ⟨⟨b,i⟩,rfl⟩:= r.assemble_bijective.2 y
    rw [r.assemble_parent,Ratio.assemble]; rw [add_comm (r.embed (b,i).1), add_sub_cancel_right]; have ht:r.assemble (0,i)=wrap _ (lift i):=by
       unfold Ratio.assemble; rw [Motion.embed_origin]; exact zero_add _
    rw [← ht,r.assemble_parent]
lemma displacedFiber (y:Site (R.family.side (m+1) p))(P: Coefficient F (V (m+1)))(hx:P.x=0) (t:ℝ)(h:P.Format y (hol G) R')(hq:P.remBound y R' (κ (m+1)) t): ∃ U: Coefficient F (V m),
    let z:=(Ratio').parent y
    U.Format z (hol G) (Q m) ∧ U.density z J (Q m) = blast H N p m d (P.density y J R') ∧ U.remBound z (Q m) (κ m) (e*t) ∧ (F).coeffSize U.x ≤ e*t :=by
    let z:=(Ratio').parent y; let z':=(Ratio').embed z
    have hSound:SectionData.Sound J (hol _) := (R.makes.sections d)
    have hn(i:ℕ):2≤(R.family.side i p).val:=by have hv:= ((H).levels.fits.sizeT i p); change _≤ (R.family.side i p).val at hv; omega
    let X:(R').activities.Moves 1 (-z'):=
      Classical.choice ((R.makes.wilson.represents N p (m+1) hm).good.labels.moves 1 _)
    let Y:(Q m).activities.Moves 1 z:=Classical.choice ((R.makes.wilson.represents N p m hm.le).good.labels.moves 1 _)
    let P':=reorient X P
    have hQ:=centralFiber hG R hm hl _ (parentRebase (d:=d) hG R hm hl y) P' (by change (F).act _ P.x = _; rw [hx,map_zero]) t
      (sub_eq_add_neg y z' ▸ rule_slide X h (hn (m+1))) (sub_eq_add_neg y z' ▸ cost_slide X hq)
    have he:=convey_slide (P:=P) (o:=y) X hSound
    rw [← sub_eq_add_neg] at he
    obtain ⟨U,hU,hF,hK,hS⟩:= hQ
    let U':= reorient Y U
    have hfin:= convey_slide (P:=U) (o:=0) Y hSound
    rw [zero_add,hF] at hfin
    have ht:=(show U'.Format z _ _ from zero_add z ▸ rule_slide Y hU (hn m))
    refine ⟨U',ht,?_,(show U'.remBound z _ _ _ from zero_add z ▸ cost_slide Y hK),?_⟩
    · rw [hfin,he]
      have hd:= play_integrable H N (B:=J) R.makes.wilson hm h hq
      funext v
      
      let f:= P.density y J R'
      have hu:(Q (m+1)).beta = (H).β N p (m+1):=rfl
      have hq' := push_pull (H) m p ((H).β N p (m+1)) 1 (-z) f hd (translate z v)
      simp_rw [pull_one, show (Ratio').embed (-z) = -z' from map_neg (Ratio').root z] at hq'
      rw [show translate (-z) (translate z v)=v from funext fun u=> congr_arg v (show (_,u.2) = u by simp [Lattice.translate])] at hq'
      exact congrArg ((((L).val:ℂ)^d) • ·) hq'
    change (F).coeffSize ((F).act _ _) ≤ _; simpa only [show (1:Signed).ortho=1 from map_one Signed.inclusionO,Frame.act_one] using hS
end Anchor
end YM.GapsR2RG
