import YM.OPE.Portfolio.Unscented
import YM.OPE.Log.Pricing
/-!
# Specific session choices, for startup Carets including ALL cut particles.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Cadet.Studio
open Function Filter Finset Lattice RG Wilson Pressure MeasureTheory
open Push Marker Accent Menu Extra.Multi Extra.Trajectories Ribbon Source Local
open Extra.Histories PhysicalNext.Repeat Lotus GridApprox.Nil OPE.Backup Motion
open Muster MergeProof.Float Labels Bid Extra.Histories.Relay Next.Rank Spindle
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{N p i j b k d :ℕ}{C:Family G}
    {W:Worth}{r:ℕ→ℕ}{L: Hol G}
    {D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}{ψ φ δ u:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}
variable (Hp:C.Makes)(L':Scrim C W u ψ φ δ ζ r D)
local notation "R"=> C.path.rep N p
local notation "H"=> C.path
local notation "F"=> C.labels.level d
local notation "T"=> C.localSection d
local notation "t"=> C.ref d
local notation "I"=> C.factory d N p
set_option quotPrecheck false
local notation "ω"=> (fun i=> Real.sqrt (C.path.levels.clock.forcedAllowance i))
-- record service wires (cannot mention `stage` resource hidden)
structure Series (C : Family G)(W : Worth)(ψ :ℕ→ℝ)(D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i))(N p d:ℕ) (E:Extra.Histories.Music (C.labels.level d) C.path N p) : Prop where
    echo : Sessions (C.localSection d) E (C.ref d) C.params W ψ D
    charge : (C.factory d N p).entries=(E.draft C.path).inits
    entrance v : profile (C.path.rep N p N).activities ((E.tone N).plays v).forced=hook (C.path.rep N p N).activities (C.path.rep N p N).p.threshold (booster (C.localSection d) (C.path.rep N p N) 0 v)
variable {E : Extra.Histories.Music (C.labels.level d) C.path N p}
include L'
lemma seriesExist (ht:C.ref d≤N): ∃ E,Series C W ψ D N p d E:=by
    obtain ⟨E,hE,hS,hC,hT⟩:= (L'.costs.aim d N p ht).lyrics; exact ⟨E,⟨⟨hS,hC,fun i=>L'.listens d N p i, L'.costs.cost,L'.costs.back⟩,hE,hT⟩⟩
namespace Series
omit L'
lemma quota (h:Series C W ψ D N p d E) (i:ℕ)(he:t ≤ i)(hp:i ≤ N) (v:C.label d): Next.UVStress.quota C d i N p v=(F).coeffSize ((E.tone i).index ((I).terminal.symm v)):=by
    unfold Next.UVStress.quota; rw [h.charge]; exact congr_arg _ ((h.echo.sung.earned i he hp).currents _)
lemma priced (h:Series C W ψ D N p d E) (i:ℕ)(he:t ≤ i)(hp:i ≤ N)(v:C.label d): Next.Rank.Spindle.paid C d i N p v=bond H N p E i ((C.factory d N p).terminal.symm v):=by
    unfold Next.Rank.Spindle.paid Price.awake Price.columns; rw [Size.smul]; dsimp only; rw [h.charge]; unfold bond; congr 1; exact congr_arg (F|>.coeffSize) ((h.echo.sung.earned i he hp).currents _)
-- Tone is linear under any aligned dictionary orientation ID
section Linear
local notation "Y"=> ((1,false):Motion)
lemma homogeneity {m:ℕ}(h:Series C W ψ D N p d E)(hp:t ≤ i)(he:i≤N){x:Site (C.side i p)} {M:Type*} (u:Finset M)(s:M→ℂ)(a:M→ (C.labels.level d).Coeff)(f:M→ Cup (C.path.rep N p i))(hS: ∀ j∈u,Mantle H N p i T Y x ((E.tone i).plays (a j)) (f j)) :
    Mantle H N p i T Y x ((E.tone i).plays (∑ i∈u,s i • a i)) (∑ i∈u,s i • f i):=by
    have he:=h.echo.sung.earned i hp he; let M':= E.tone i; have hr(x):= he.earns x|>.2
    constructor
    · let g (x:(F).Coeff):=(M'.plays x).exponentialEntry 0 (T) (R i); have hh:IsLinearMap ℂ g:=expoLinear _ _ he.book hr
      let L:=(IsLinearMap.mk' g hh); rw [show ((E.tone i).plays (∑ i∈u,s i • a i)).exponentialEntry _ _ _ = _ from map_sum L (fun i=>s i • a i) u,Cup.summing]; simp_rw [map_smul L, Cup.home_smul]; funext U; unfold radiant stepUp; simp_rw [Finset.sum_apply,Pi.smul_apply]
      change _ = (alto H i d)*∑ j∈u,s j * g (a j) (pull 1 x U); rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j hj=>?_); rw [(hS j hj).prose]; exact mul_left_comm ..
    let g (x:(F).Coeff):=profile (R i).activities (M'.plays x).forced; have hh:IsLinearMap ℂ g:=inkL _ _ he.book hr
    let L':=IsLinearMap.mk' g hh; unfold sunny; rw [show profile _ ((E.tone i).plays (∑ i∈u,s i • a i)).forced= _ from map_sum L' (fun i=>s i • a i) u,Cup.summingKey]; simp_rw [map_smul L',Cup.leaves_smul]
    funext j U; unfold floatUp stepUp; simp_rw [Finset.sum_apply,Pi.smul_apply]; change _ = (alto H i d)*∑ k∈u,s k * g (a k) ((puff Y x).symm j) (pull 1 x U); rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b hb=>?_ ; rw [(hS b hb).key]; exact mul_left_comm ..
end Linear
include Hp L'
-- start from k at fully centered leaf. Pricing uses true Notes
lemma launch (h:Series C W ψ D N p d E) (a:C.label d){w:ℝ}(X:∀ i,Site (C.side i p))
    (he:t≤ k)(hp:k≤N)(hx:0<w)(hr:w*Spindle.paid C d k N p a≤ζ d k)(hK:∀ i:ℕ,k ≤ i→ i<N → X (i+1)=(C.path.levels.clock.op i p).ratio.embed (X i)): ∃ A, Program H N p k N X A (stair φ w k) D le_rfl ∧ Entrance H N p (X N) (A N) (C.O N p a (X N)) (stair φ w k N) (u N) ∧
    ∀ i,k ≤ i→i ≤ N→ Mantle H N p i T (1,false) (X i) ((E.tone i).plays ((I).terminal.symm a)) (A i):=by
    let V:=(I).terminal.symm a; let F':= soarF H T N p E V (1,false) X; let Q:=stair φ w k; obtain ⟨b,hQ,hC,hB,hb,hH⟩:= L'.costs.heights d k N p he hp
    have hZ: Sung (T) H N p C.params W k E:= ⟨h.echo.sung.head,hp,fun i h'=>h.echo.sung.earned _ (he.trans h'),fun i h'=>h.echo.sung.step _ (he.trans h')⟩
    have hϑ:Brine H k δ φ:=⟨fun i _=> L'.costs.stay.water i (Nat.zero_le _),fun i _=>L'.costs.stay.mint i (Nat.zero_le _),fun i _=> L'.costs.stay.split i (Nat.zero_le _),fun i _=> L'.costs.stay.support i (Nat.zero_le _)⟩
    have hk(i:ℕ)(he:k ≤ i):0<Q i:=march_pos _ _ _ _ _ (fun _=>hx) hϑ _ he Unit.unit
    have he'(i:ℕ)(he:k ≤ i): Q (i+1)=φ i*Q i:= by unfold Q stair; rw [march,if_pos he]
    have hm : ∀ i,k ≤ i → i≤N→ Q i*bond H N p E i V ≤ ζ d i:=by
       apply cost_chain H C.params (C.localSection d) W (ζ d) k N p E V Q le_rfl (fun i he _=>(hk i he).le) hp _ (fun i hi _=> hk i hi) L'.costs.cost L'.costs.back hZ
       · rw [show Q k=w from congr_fun (marines k φ (fun _:Unit=>w) (fun _=>hx)) ()]; rw [h.priced k he hp] at hr; exact hr -- separate rw
       intro i he hi; rw [he' i he]; exact le_trans (le_of_eq (b:=φ i* (((C.S.block i).val:ℝ)^d * (C.path.levels.params (i+1)).columns)*ζ d i*Q i) (by ring)) (mul_le_mul_of_nonneg_right (hC.cost i he) ((hk i he).le))
    have hs: ∀ i:ℕ,k ≤ i →∀ hi:i<N,Carol T H N p i (D N p i hi) (E.tone (i+1)) (E.tone i) (ψ i)∧ SoundDoor (C.path.levels.clock.op i p) (D N p i hi):= fun i hI hi=>⟨h.echo.songs i (he.trans hI) hi,(h.echo.stamps i (he.trans hI) hi).choose_spec.tuned.2.1⟩
    obtain ⟨g,hg,hU⟩:= stater H C.params (T) W (ζ d) u ψ b k N p E V (1,false) X Q D Hp.wilson (Hp.sections d) hZ (fun i he _=> hk i he) (fun i he hᵢ=> (he' i he).trans_le (mul_le_of_le_one_left (hk i he|>.le) (hC.level _ he))) hm hQ hB hb hH hK (h.entrance V) hs
    -- edit placeholders rotate
    let A(i):Cup (R i):= if hi:k ≤ i∧i≤N then Cup.book (R i) (F' i) (g i) (hg.stocked i hi.1 hi.2) else 0
    have hΓ (i:ℕ)(he:k ≤ i)(hn:i≤N): A i=Cup.book (R i) (F' i) (g i) (hg.stocked i he hn):= dif_pos ⟨he,hn⟩
    have hz(i:ℕ)(he:k ≤ i)(hn:i≤N): (A i).pays= coin (R i) (F' i) (g i):= Cup.booked (Hp.wilson.represents N p i hn|>.good.labels) _ _ _ _ (hΓ i he hn)
    refine ⟨A, ⟨fun i hi hn=>?_⟩,?_,fun i hi hn=>?_⟩
    · obtain ⟨μ,v,x,b,hM,hξ,hB,hT,hU⟩:= hg.sways i hi hn; have hY:=hi.trans i.le_succ; refine ⟨v,⟨?_,μ,x,b,hM,hξ,hB,hT,?_⟩⟩; · rw [hz i hi hn.le,hz _ hY hn]; exact (hg.feeds i hi hn).symm
      rw [hΓ i hi hn.le,hΓ _ hY hn]; exact hU
    · refine ⟨fun U=> ?_,?_⟩; · erw [← Ribbons.itemT C N _ _ Hp a (X N), hz N hp le_rfl]; exact hg.writes U
      obtain ⟨ψ,h,hp',hX,hU⟩:= hg.patent; refine ⟨ψ,h,hp',hX,?_⟩; rw [hΓ N hp le_rfl]; exact hU
    · rw [hΓ i hi hn]; exact ⟨rfl,hU i hi hn⟩
    -- placeholders if no access edit
end Series
end YM.MergeProof.Ribbons.ManyCopies.Cadet.Studio
