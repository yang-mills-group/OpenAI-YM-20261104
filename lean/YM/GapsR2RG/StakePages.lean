import YM.GapsR2RG.StakeLedger
/-! # Expose full +2 regular-label price for the actual Piano response by aggregation and exact orbit restoration.
Compare the `Matric.Tool.stained` argument; ancestor/gas forced labels not changed by this estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Matric
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{H:History G} {N p m:ℕ}{Y:Hol G}{B:SectionData F}

lemma Staked.joins {c:Side}{R:Rep G c}{ι:Type*}(P:ι→ Coefficient F c)(e:ℕ ≃ ι×ℕ) (v:ι→ℝ) (h:∀ i,Staked (P i) R (v i))(hv:Summable v): Staked (Extra.Histories.merge e P) R (∑' i,v i):=by
    let K:=turnCost R.p.order R.p.power; have hk:0<K:=by unfold K turnCost; positivity
    choose a ha hc using h; have hj i := by have hv:= (le_div_iff₀ hk).mpr ((mul_comm _ K).trans_le (hc i)); exact le_trans (a:=‖a i‖) (b:=a i) (Real.norm_of_nonneg (Blown.price (ha i))).le hv
    have hx:Summable a := (hv.div_const K).of_norm_bounded hj
    refine ⟨_,Blown.joins e ha hx,?_⟩; rw [←tsum_mul_left]; exact (hx.mul_left K).tsum_le_tsum hc hv

variable {u ζ t:ℝ}
variable (P:Tool F H N p m) {W:Worth}{D:GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}{T:Heading F}{X:Set Wing}
variable (h:Tool.Cap P B Y W D T u ζ t X) (hs:Reserves H N p m Y P.plate u ζ) {S:Desk G (H.S.side (m+1) p)}(hw:Well (H.rep N p (m+1)) S (Real.sqrt (H.levels.clock.forcedAllowance (m+1))))
variable (Q:F.Index→ Coin F Y S) (hQ:∀ i, ‖Q i‖≤(H.levels.params (m+1)).columns * F.coeffSize (F.core (Size.axis F i)))
set_option quotPrecheck false
include W
include P h hs hw hQ
local notation "E'"=> H.rep N p (m+1)
local notation "R'"=> H.rep N p m
local notation "b'"=> H.S.block m
local notation "Z!"=> P.plate
open InputColumn

omit hQ in
private lemma shots_funded (i:F.Index) {Z:ℝ}(hiV:‖Q i‖≤Z) : let x:= Size.axis F i; Staked (P.shot i (Coin.uses (Q i))) (R') (u*F.coeffSize (vowel F (b') (F.core x))+ζ*Z):=by
 intro v; let A:= book v (Coin.uses (Q i)); let U₀:= E'; obtain ⟨hE,hc⟩:= granted hw Y v (Q i); let K:= P.up; let I:= rack P.up A
 have hx:I.x=v:=rfl; have hf:I.Format 0 Y U₀:=rack_format K A hE; have hk := h.shines.represents N p (m+1) h.late|>.good
 obtain ⟨l,r,ha,hb,hS,-,⟨a,hA,hA'⟩,b,hB,hB'⟩:= keeps K A hc
 let δ := Real.sqrt (H.levels.clock.forcedAllowance (m+1)); have h0:0<δ:=Real.sqrt_pos.mpr (forcedPos ..)
 let g i:=U₀.p.mass (I.support i) (a i); let k i:=(U₀.p.mass (U₀.activities.forced i).support (b i))/δ
 let c' := u * F.coeffSize (vowel F (b') (F.core v)); let W:=consist c' (fun i=>ζ*g i) (fun i=>ζ*k i)
 let X:=tell ∘ Matric.tags (Z!) K A i
 have Hk:SumBudget k r:=by
    refine ⟨fun i=>div_nonneg (hB.1 _) h0.le,hB.2.1.div_const _,?_⟩; unfold k; rw [tsum_div_const]; exact (div_le_iff₀ h0).mpr (hB.2.2.trans_eq (mul_comm ..))
 have hp (j):Staked (X j) (R') (W j):=by
    rcases j with j|j|j
    · exact hs.main i
    · let s:=mapSeat (n:=H.S.side (m+1) p) j
      exact hs.regular _ _ (a j) ⟨hf.smooth j,hf.origin _,hf.identity_null _,hf.projects _⟩ (hA' _) -- supports defeq
    by_cases ht : I.forced j=0
    · have he : Blown (book (0:F.Coeff) 0) 0 (R') 0:=by
          refine ⟨0, ?_,(fun i=> (regular0 (n:=H.S.side m p) (R').p (mapSeat i) 0).2)⟩
          simp_rw [Pi.zero_apply,Push.Local.reservedMass,mul_zero]; exact Push.Local.sumBudget_zero (le_refl _)
      change Staked (tell ((Z!).ink j (I.forced j))) _ (ζ * _); rw [ht,h.copies.blank]; exact ⟨0,he,(mul_zero _).trans_le (mul_nonneg h.budget.epsilon (Hk.1 j))⟩
    exact hs.forced j _ (b j) ht ⟨hf.invariant j,hf.borel j,hf.supported j,hf.carried j,hf.forcing j⟩ (hB' j).1 (hB' j).2
 let t':=(∑' i,g i)+(∑' i,k i); have h':t'≤Z:= ((add_le_add hA.2.2 Hk.2.2).trans hS).trans hiV
 have hw:HasSum W (c'+ζ*t'):= by unfold t'; rw [mul_add]; exact added (hA.2.1.hasSum.mul_left _) (Hk.2.1.hasSum.mul_left _)
 have h':= le_trans hw.tsum_eq.le (add_le_add_right (mul_le_mul_of_nonneg_left h' h.budget.epsilon) c')
 exact (Staked.joins X (code Listing) W hp hw.summable).more h'

local notation "U"=> (H.levels.params (m+1)).columns
local notation "W₀"=> fun (v : F.Coeff)=>F.coeffSize (vowel F (H.S.block m) (F.core v))
local notation "b₁"=> u+ζ*(U)

private lemma portfolioFunded (i:Tally F) : Blown (P.portfolio Q i) 0 (R') ((b₁)*W₀ (Size.axis F i.2)):=by
   let s:=P.shot i.2 (Coin.uses (Q i.2)); let x:=Size.axis F i.2; let w:=W₀ x
   have hT := Work.G08.size_vowel F (H.S.block m) (F.core x)
   have hv i:0≤ (H.levels.params i).columns:=zero_le_one.trans (H.levels.params i).columns_ge
   have hx: ‖Q i.2‖ ≤ (U)*w:= (hQ i.2).trans (mul_le_mul_of_nonneg_left hT.1 (hv _))
   obtain ⟨a,ha,he⟩:=shots_funded P h hs hw Q i.2 hx
   have hF:s.Format 0 Y (R'):= (P.recoil h hw i.2 (Q i.2)).earns.format
   have hp(n:ℕ): 2 ≤ (H.S.side n p).val:= (by decide:2≤4).trans (Next.Foundations.actual_side_ge H.S n p)
   have hF':= (Blown.spin ha (P.whirl i.1) hF (hp m)).enlarge (he.trans_eq (show _=(b₁)*w from by rw [add_mul,mul_assoc]))
   rw [show affine i.1.1 (0:Site (H.S.side m p)) 0=0 by simp [affine]] at hF'
   exact hF'

lemma Tool.pagesBlown (v:F.Coeff) : Blown (P.pages Q v) 0 (R') ((b₁)*orbitCost F * W₀ v):=by
    have hf : ∀ i:Tally F, _ := portfolioFunded P h hs hw Q hQ -- inspect
    have hc : 0 ≤ b₁ := by have hv:0≤ (U):=zero_le_one.trans (H.levels.params (m+1)).columns_ge; have hz:=h.budget.epsilon; have hu:=zero_le_one.trans h.budget.cost; positivity
    exact Blown.enlarge (Blown.pencil_joins (code _) hf (chips F) v) (residual_bill F (H.S.block m) (b₁) hc v)

omit hQ in
theorem Gram.pointBlown (Q : Matric.Gram F Y S ((H.levels.params (m+1)).columns))(hr:roomCost H.levels W) (hb:Bank W H.levels) (v:F.Coeff):
   Blown (Q.point P v) 0 (R') ((H.levels.params m).columns * F.coeffSize (F.core (Q.point P v).x)) :=by
   let Q' := Q.scythe
   have hZ(i): ‖Q' i‖≤(H.levels.params (m+1)).columns * F.coeffSize (F.core (Size.axis F i)):= Q.toll _
   obtain ⟨hv,hQ,hx⟩:= P.stained h hw Q.scythe hZ v; obtain ⟨hf,hp,-⟩:= Work.G08.cone_step W H hr hb m F _ _ _ _ hx le_rfl
   exact (Tool.pagesBlown P h hs hw Q.scythe hZ v).enlarge hf
end YM.MergeProof

