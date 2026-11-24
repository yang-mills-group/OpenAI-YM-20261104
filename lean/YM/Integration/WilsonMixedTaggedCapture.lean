import YM.Integration.WilsonMixedTaggedPhysical
import YM.Integration.WilsonMixedTaggedMeasuredBudget
import YM.Integration.WilsonMixedTaggedSpend

/-! Joint lower-date comparison of the true finite Wilson columns and their
stripped input. The entire unweighted error precedes every held field,
regulator and period on the original physical calendar. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMixedTaggedCapture
open Filter Finset Function Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker RG05Readout
open RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station OPE
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G) {W:Type} [DecidableEq W] [Fintype W]
local notation "C₀" => R.family

/-- The comparison keeps the original full UV start and the exact stripped
restoration, plus both represented arrays and their unweighted site sums. -/
def Delivered {n t N per:ℕ} (b:ℕ) (tN:t ≤ N)
    (o:W → Site ((C₀).side n per)) (E:W → Motion) (s:W → ℕ) (q:ManyStem C₀ o n → Body)
    (P:(v:W) → Sight C₀ (s v) per) (S:(v:W) → Emblems C₀ (s v)) (x:(v:W) → Palette C₀ (s v))
    (roster:Census W) (cash:ℝ) : Prop :=
  let A:=Mine.tree o E
  let J:=Mine.ward o E roster
  let Y:=(C₀).path.rep N per
  let rows:=imprint R.makes A (headings o E q) (plants (m:=t) s P S x)
  let expo:=fun i:ℕ=>if i=t then ((C₀).path.levels.budget i).supportExponent-4
    else ((C₀).path.levels.budget i).supportExponent
  ∃ F L:(i:ℕ) → Config G ((C₀).side i per) → Poly (J i),
    Replay A s (le_refl n) t F N ∧ Replay A s (le_refl n) t L N ∧
    (∀j:ℕ,n ≤ j → ∀jN:j ≤ N,F j=gust (C₀).path N per N
      (birth (J j) (Y N) (WilsonMixedTaggedFields.columns o E s q S x t N j)) j jN) ∧
    L t=restore (Y t) (fun v=>(rows t tN v).2.1)
      (fun v=>profile (Y t).activities (rows t tN v).2.2)
      (0:Support ((C₀).side t per) → Config G ((C₀).side t per) → Poly (J t)) 0 ∧
    ∀j:ℕ,b ≤ j → ∀jt:j ≤ t,WilsonMixedTaggedSession.Matched (B:=J j)
      (Y j) (rows j (jt.trans tN)) (A.supportX j) (fun _=>1) (expo j) cash (F j) (L j)

private theorem at_date {n b t N per d k h D₀:ℕ} (nb:n ≤ b) (bt:b+1 < t) (tN:t < N)
    (o:W → Site ((C₀).side n per)) (E:W → Motion) (s:W → ℕ) (q:ManyStem C₀ o n → Body)
    {rail:Address.Rail C₀} {worth:Worth} {rates:ℕ → ℕ} (book:OPE.Package C₀ worth rates rail)
    (stock:Storage C₀ rail) (P:(v:W) → Sight C₀ (s v) per) (S:(v:W) → Emblems C₀ (s v))
    (x:(v:W) → Palette C₀ (s v)) (roster:Census W) {Q cash:ℝ} {capbook:ℕ → ℕ → ℝ}
    (ready:Warm C₀ n (d+1) k) (slots:Fintype.card W*2 ≤ (C₀).path.levels.clock.J n)
    (spine:∀v,Spine rail capbook R.makes n per (s v) N (P v) (S v)) (degree:∀v,s v ≤ d)
    (caps:∀v:ManyStem C₀ o n,Cap (s v.val.1+2) (q v) 1) (qp:0 < Q) (charge:∀v,size (x v) ≤ Q)
    (qh:Q ≤ ((C₀).path.levels.clock.hatBeta t)^h) (clear:Clearance o E s (headings o E q) roster t)
    (room:let B:=((C₀).path.levels.budget t).B; D₀*(4*B+2)+2*B ≤ B^2) (cash0:0 ≤ cash)
    (paid:∀j:ℕ,b ≤ j → j ≤ t → ∀a:(Mine.ward o E roster j).Mode,
      Real.exp (-(D₀:ℝ)) ≤ cash*Poly.toll (fun _=>envelope C₀ t (d+1) k Q j) a) :
    Delivered R b tN.le o E s q P S x roster cash := by
  cases t with
  | zero => omega
  | succ m =>
    obtain ⟨F,L,first,second,known,head,ledger⟩:=
      WilsonMixedTaggedPhysical.original R o E s q book stock P S x roster (show n ≤ m by omega)
        tN ready slots spine degree caps qp charge qh clear room
    refine ⟨F,L,first,second,known,head,?_⟩
    intro j bj jm
    obtain ⟨H,H',K,K',a,a',u,u',regular,forced⟩:=ledger j (nb.trans bj) jm
    have pos:0 < envelope C₀ (m+1) (d+1) k Q j :=
      mul_pos (rust_paid _).1 (grantw (totalpos qp j))
    exact ⟨H,H',K,K',a,a',u,u',
      WilsonMixedTaggedUnweight.original regular (fun _=>pos) (Real.exp_pos _) cash0
        (fun _ _ v _=>paid j bj jm v),
      WilsonMixedTaggedUnweight.original forced (fun _=>pos) (Real.exp_pos _) cash0
        (fun _ _ v _=>paid j bj jm v)⟩

/-- A fixed genuine menu can be chosen before the radius. At that radius
one traversal pays both forms of error for every eligible physical input. -/
theorem original (simple:G.Simple) (K n d k h p:ℕ) (hk:0 < K) {ε:ℝ} (ep:0 < ε)
    (slow:∀j,(((C₀).S.block j).val:ℝ) ≤ Real.log (RG05Readout.Lambda (C₀).path.levels j)) :
    ∀ᶠ r in 𝓝[>] (0:ℝ),let b:=crossLevel (C₀).S r-1-1
      let t:=WilsonMeasuredWindow.stop (C₀).path.levels simple K r
      let B:=((C₀).path.levels.budget t).B
      ∃ D₀:ℕ,D₀*(4*B+2)+2*B ≤ B^2 ∧ ∀N:ℕ,∀tN:t < N,∀per:ℕ,
        ∀(o:W → Site ((C₀).side n per))(E:W → Motion)(s:W → ℕ)(q:ManyStem C₀ o n → Body)
          {rail:Address.Rail C₀}{worth:Worth}{rates:ℕ → ℕ}(_book:OPE.Package C₀ worth rates rail)
          (_stock:Storage C₀ rail)(P:(v:W) → Sight C₀ (s v) per)(S:(v:W) → Emblems C₀ (s v))
          (x:(v:W) → Palette C₀ (s v))(roster:Census W){Q:ℝ}{capbook:ℕ → ℕ → ℝ},
          Warm C₀ n (d+1) k → Fintype.card W*2 ≤ (C₀).path.levels.clock.J n →
          (∀v,Spine rail capbook R.makes n per (s v) N (P v) (S v)) → (∀v,s v ≤ d) →
          (∀v:ManyStem C₀ o n,Cap (s v.val.1+2) (q v) 1) → 0 < Q → (∀v,size (x v) ≤ Q) →
          Q ≤ ((C₀).path.levels.clock.hatBeta t)^h → Clearance o E s (headings o E q) roster t →
          Delivered R b tN.le o E s q P S x roster (ε*((Real.sqrt ((C₀).path.rep N per t).beta)⁻¹)^p) := by
  have dates:=WilsonMixedTaggedMeasuredWindow.original R simple K hk slow
  have purchase:=WilsonMixedTaggedMeasuredReserve.original R simple K (d+1) k h (Fintype.card W) p hk ep slow
  filter_upwards [dates.2,purchase,(WilsonMixedTaggedSpend.lower R).eventually_ge_atTop n] with r calendar receipt nb
  intro b t B
  obtain ⟨D₀,room,_,wallet⟩:=receipt
  refine ⟨D₀,room,?_⟩
  intro N tN per o E s q rail worth rates book stock P S x roster Q capbook ready slots spine degree caps
    qp charge qh clear
  apply at_date R nb calendar.1 tN o E s q book stock P S x roster ready slots spine degree caps
    qp charge qh clear room (by positivity)
  intro j bj jt a
  have one:1 ≤ ((C₀).path.levels.clock.hatBeta t)^((k+h)*Fintype.card W) :=
    one_le_pow₀ ((C₀).path.levels.fits.delayed t).le
  exact (le_mul_of_one_le_left (Real.exp_pos (-(D₀:ℝ))).le one).trans
    (wallet N tN.le per j bj jt (fun _=>Q) (fun _=>qp) (fun _=>qh) a
      (WilsonMixedTaggedMeasuredBudget.cardinal roster ((Mine.tree o E).labelY j) a))

end YM.Integration.WilsonMixedTaggedCapture
