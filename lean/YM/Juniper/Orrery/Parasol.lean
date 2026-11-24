import YM.Juniper.Orrery.Gondola
/-!
 # On the real Φ schedule consume periodic PT renderer; keep requested
 budgets even after long-path pruning & lifts. Still need Lens generation;
 given this `after` it doesn't ask any output realization other than Phantasmal Fixed price.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Orrery
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Further.PhysicalPeriodLimitF933 Macrame Deck Flare
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost Org Input Supply Slide
open Progress.DirectedRecipe UVExtension Oriel Dales Tour Height Averaging
open Whirl Ovens Ovens.Pipes Rack Voucher Rain Time Bright Charted Lamppost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {c C:Side} {k n:ℕ} {ρ χ η:ℝ} (P:BudgetPoint)
variable {X : Metals G} {D:Rolls X.p}{A:Alloy X D} (R: Factor A)
section post
variable (hm:C.val=c.val*k)(T : Orrery.Model G P ρ)(S: PathData G)(V: Clip)(α: ℝ)
  (hB:2 ≤ P.B)(h:Margin P c) (hG:G.Simple)
local notation "F"=> (T.frames C)
local notation "H"=> (T.frames c)
local notation "Q"=> posting
local notation "D"=> (posted P (T.frames c) S V α)
local notation "J"=> (posted P (T.frames C) S V α)
local notation "u"=> (numbering (Collection.EKey c))
local notation "U"=> (numbering (Collection.EKey C))
include hB hG hm h T
lemma boarding (j:ℕ) : ∃ p:ℕ→ℕ, Leaves hm p (J|>.root) (J|>.field) (D|>.root) (D|>.field) (places P F S j) (places P H S j):= by
    obtain ⟨p,hp⟩:= T.edges c C k hm h; have hz:= stepping P S (hC:=hm) H F hp (T.dear c h) (T.dear C (Orrery.wider hm P h)) h hG j hB V α; let l(i:ℕ):= (numbering (Collection.EKey c)).symm (casting hm p ((numbering (Collection.EKey C)) i))
    have he {n:Side} (W:Curtain G n)(x:ℕ): x∈places P W S j ↔ numbering (Collection.EKey n) x∈ visiting P S W j:=⟨fun h=> by obtain ⟨i,hi,rfl⟩:= mem_map.mp h; simpa only [Equiv.toEmbedding_apply,Equiv.apply_symm_apply] using! hi,fun h=> Finset.mem_map.mpr ⟨_,h,Equiv.symm_apply_apply ..⟩⟩ -- first simp using hi maybe reduces
    have hh i: u (l i) = casting hm p (U i):= (u).apply_symm_apply _
    refine ⟨l,?_,?_,?_,?_,?_⟩
    · intro i hi; have hv:= hz.root (U i) ((he F i).1 hi); exact ⟨(he H _).2 (hh i ▸ hv.1), show _=(incoming (H|>.book) S P (u (l i))|>.site) from hh i ▸ hv.2⟩ -- ▸ wrong orientation
    · intro i hi; change (incoming (H).book S P (u (l i))).support=_; rw [hh]; exact hz.stable (U i) ((he F i).1 hi)
    · intro i hi W; change _= archive (H).book S V (H).stamp α _ (u (l i)) _; rw [hh]; exact hz.truer (U i) ((he F i).1 hi) W -- H.book notation
    · intro i x hi hx; obtain ⟨p,hp,hx',hl⟩:= hz.serves (u i) x ((he H i).1 hi) hx; refine ⟨U|>.symm p,(he _ _).2 (by rw [Equiv.apply_symm_apply]; exact hp), (u).injective ?_,?_⟩; · rw [hh, Equiv.apply_symm_apply,hx']
      change (incoming _ S P (U ((U).symm p))).site=x; rw [Equiv.apply_symm_apply]; exact hl
    intro i k hi hk hh' h; apply (U).injective; refine hz.uniqueness _ _ ((he _ _).1 hi) ((he _ _).1 hk) hh' ?_; rw [← hh i,← hh k,h]
end post
section chart
variable {i j:ℕ} (M:Orrery.Model G P ρ)
lemma lyrics (j:ℕ)(hs:P.B ≤ j)(hv:Margin P c)(hw:Margin P C): Trio.Compatible ((M.frames c).root) ((M.frames C).root) P j:= by
    intro i i' V V' hV hV' hW; let R':=c*C; let p:=M.frames c; let q:= M.frames C; let u :=M.frames R'; have hR: R'.val=c.val*C.val:=rfl; have hR':R'.val=C.val*c.val := Nat.mul_comm ..; let u₁:=Lattice.translate i V; let u₂:=Lattice.translate i' V'; obtain ⟨θ,hθ⟩:=M.edges c R' C.val hR hv; obtain ⟨Ψ,hΨ⟩:= M.edges C R' c.val hR' hw
    let u₃:=(Macrame.normal (Deck.divides hR) hR).links u₁; let u₄:=(Macrame.normal (Deck.divides hR') hR').links u₂; have hΩ : Margin P R':=Orrery.wider hR P hv
    have ht : u.root 0 u₃= u.root 0 u₄:= by
       apply (Curtain.pose (M.dear R' hΩ) 0).sites _ _ (readNear 0 (by unfold Margin at hΩ; omega) ?_); unfold u₃ u₄ u₁ u₂; rw [Slide.rolls,Slide.rolls,map_zero,map_zero,increases,increases]; have hX : Lattice.box P.B ⊆ Lattice.box j := by intro i hi; obtain ⟨ha,hb⟩:=box_test.mp hi; exact box_test.mpr ⟨fun v=>(show -((j:ℕ):ℤ) ≤ -(P.B:ℤ) by omega).trans (ha v),fun v=>(hb v).trans (by exact_mod_cast hs)⟩
       exact fun i hi hi'=> hW i (hX hi) (hX hi')
    have he:= Orrery.root_cost hR 0 p u hθ u₁; have hq:= Orrery.root_cost hR' 0 q u hΨ u₂; rw [map_zero] at he hq; have hh : p.root 0 u₁=p.root i V:=by unfold u₁; rw [← pull_one]; simpa only [p,Lattice.affine,Signed.act_zero,zero_add] using (Curtain.mirrors (M.dear _ hv) 0 1 i V)
    refine hh.symm.trans (he.symm.trans (ht.trans (hq.trans ?_))); unfold u₂; rw [← pull_one]; simpa only [q,Lattice.affine,Signed.act_zero,zero_add] using (Curtain.mirrors (M.dear _ hw) 0 1 i' V')
local notation "V"=> M.frames
lemma lives (hi:P.B ≤ j) (hm:Margin P c): Curtain.TidyC (M.frames c) P j ρ:= by
    have he:=M.dear c hm; refine { he with frames:= fun i h k hk=> (neighbors_mem ..).2 (((neighbors_mem ..).1 (he.frames i h hk)).trans hi) }
end chart
section actual
variable {N m n r:ℕ} {ε:ℝ} (H : Tour R N m n ε) (h: Guild.Paperwork R.shape ε Camp.soft A.delay)
                (hT:Tailcoat X.p D A.delay) (hG:G.Simple)
local notation "W"=> A.B.a
local notation "L"=> ((W).clock)
local notation "B"=> A.B.a.budget m
local notation "S"=> A.B.kin.path N m
local notation "S!"=> Bright.sews R m
local notation "p"=> A.B.a.params m
local notation "v"=> (p).clip
local notation "α"=> A.B.kin.alpha N m
local notation "Φ"=> A.B.a.S.side m n
local notation "τ"=> (L).hatBeta m
local notation "g"=> (L).allowance m
local notation "b"=> (τ^r)⁻¹
local notation "K"=> ((2*rim)*forecastE W m)
local notation "M"=> (miner R m)
local notation "N'"=> Meadow.studio M (radiusB τ)
variable (T:Orrery.Model G (A.B.a.budget m) ((2*rim)*forecastE A.B.a m))
abbrev chair_small (P:BudgetPoint) (z:ℕ)(i:Stars): Margin P (Trio.fence z P.B i):= (show 50*(1+P.B) ≤ 100*(1+P.B) by omega).trans (Trio.highChair z P.B i).2 -- macro P conflict
lemma scenery (hq:2*Bright.home R m< (Φ).val): Flare.Layout (n:=n) (m:=m) R (T.frames (Φ)) (fun i=>T.frames (caves R m i)):= by
    let u:= T.frames; have hv i : Margin B (caves R m i):=Orrery.chair_small (B) _ i; have he: Margin B (Φ):= by unfold Bright.home Trio.base Trio.tent at hq; change 50*(1+radiusB τ)≤ _; omega
    have hp : (B).B ≤ N':= (show _ ≤ 2*(B).B by omega).trans (Bright.climb («b»:=(R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).halo) (n:=mast ((L).J (m+1))) (j:=(B).B) ((B).B_pos)|>.2.1); let w:= u (Φ); exact ⟨lives (B) T hp he,fun i=> lives (B) T hp (hv i),fun i=> Curtain.mirrors (T.dear _ (hv i)),fun i j=> lyrics (B) T N' hp (hv i) (hv j),fun i=> lyrics (B) T N' hp (hv i) he, fun i=> (Curtain.pose (lives (B) T hp he) i).sites⟩
include H h hT hG
local notation "χ"=> ((rim/8)*b*g)
set_option maxRecDepth 6000 in
noncomputable def after (hk:powerUp r≤(L).J (m+1)) : Canister G B g χ:= by
    have hh:=(L).hatBeta (m+1); let β:= (L).hatBeta (m+1); have hβ:β∈Rain.lands A m:=by change β/2 ≤ β∧ β≤ 2*β; have ht:1 < β:= A.B.a.fits.delayed _; constructor <;> linarith
    have hp:= Bright.here R H.hm hβ 0; have hr : 2 ≤ (B).B:= hp.decent.radius
    refine ⟨fun c=> posted (B) (T.frames c) S v α,fun c z=> places (B) (T.frames c) S z,fun n hn=>?_,fun n _=>?_,fun c C k hC hv n=> ?_,fun n hu=>?_,fun n hu=>?_ ⟩
    · exact Orrery.active_post B _ _ _ _ (T.dear _ hn) hp.decent -- notation open
    · exact Orrery.applause (B) (T.frames n) S v α
    · exact Orrery.boarding B hC T S v α hr hv hG n
    · let p':= T.frames n; have hv:= Orrery.validPost B _ _ _ α (T.dear _ hu) (A.B.support.cap N m H.hm.le) hp.decent hp.width hG hu; have hy:0≤g:= (Dales.fundedP m W|>.1.le); exact { hv with boundE:= VerifiedReset.Time.E_rises hv.boundE ((Orrery.viewH R H h).trans (mul_le_of_le_one_left hy (by norm_num [rim]))) }
    exact Orrery.sold R H h hT _ (T.dear n hu) hk hG -- order
-- labels
lemma after_post (hk: powerUp r ≤ (L).J (m+1)): (Orrery.after R H h hT hG T hk).prior c= posted B (T.frames c) S v α:= rfl
end actual
end YM.Juniper.Orrery
