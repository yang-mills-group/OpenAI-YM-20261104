import YM.RG16.Unmasked.Merits

/-!
# Physical root bound of the actual canonical OPE report

Use replica BOTH for z and its priced reference correction to the true
pi fit. After exiting this theorem `x` is not a separately existentially
manufactured reader. It is the same `topReport` of the full unmarked/slot
test defined from **only** C.path, its bare Gibbs data, and the actual Pi.
No perturbative data assumed. Actual perturbative-precision step can start
on the `Booked` member living on the full physical curve.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG16.Literal
open Function Set Filter MeasureTheory OPE Lattice Wilson RG Source Overlay Bid MergeProof Accent
open Ribbons ManyCopies Cells Extra.Histories Push.Local
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
open scoped Topology Matrix.Norms.Frobenius Classical BigOperators ContDiff
variable {G : Gauge} (C: Family G) (hG:G.Simple){W r D} (L:Package C W r D)
set_option quotPrecheck false
local notation "P" => C.path.levels
local notation "σ" => C.S.scale
local notation "F" => C.labels.level
open Trace.Physical.GermGraph
variable (h:C.Makes) {I : Type} [Fintype I][DecidableEq I] [Nonempty I] (d : I→ℕ)(p N b k e J u:ℕ)
  (Gm : ℕ→ℝ) (hGm : RateIs atTop C.S.scale Gm 0)

local notation "Y" => (center C.S p) -- no
variable (η M A:ℝ) (hη:0<η)(hM:0<M)(hA:20<A)
  (hpace : ∀ i,((C.S.block i).val:ℝ) ≤ Real.log (Lambda C.path.levels i))
local notation "S" => port C (8*M) A (mul_pos (by norm_num) hM)

def discrepancy (hu : Opened C e u p)(hN:u ≤ N)(f:Cut C N p) :=
    f - C.O N p ((C.factory e N p).terminal (topReport C N p e h u hu hN f)) 0

-- Optional choose a pair for stable reference application (choose once prior to jobs)
structure Stop : Prop where
   live : Stock.Tabs.opens C.path.levels 1 J u
   height : C.ref e ≤ J
   doors (p:ℕ) : Opened C e u p

include L hG in
theorem forStop (d':ℕ) : ∀ᶠ j:ℕ in atTop,∃ u:ℕ,∀ e'≤ d',Stop C e' j u:= by
   have he : ∀ᶠ j:ℕ in atTop,∀ i ∈ Finset.range (d'+1),∀ p, Opened C i j p :=
      eventually_all_finset ..|>.2 (fun i _=> open_late C hG i)
   obtain ⟨n,hn⟩:= eventually_atTop.mp he
   filter_upwards [eventually_ge_atTop n] with j hj
   let b := Stock.Tabs.chosen C.path.levels 1 L.tabs j
   have hb:= Stock.Tabs.opened C.path.levels 1 L.tabs j
   refine ⟨b,fun i hi=>?_⟩
   have hv:= Finset.mem_range.mpr (Nat.lt_add_one_iff.mpr hi)
   exact ⟨hb,(hn j hj i hv 0).post,hn b (hj.trans hb.1) i hv⟩

include hG hGm hη hA hpace L
/-- All expenses retained for later packed comparisons, with independent-germ
version. In a physical label reading after using this result keep TWO scales:
the candidate has been intrinsically generated and propagated all the way
down this exact history. The only perturbative computation still has to be on
an independent prescription at k, not fitted from this.
We don't expose ancillary RF-label genealogy to
phase predictions; expose exact test & norm instead. -/
theorem finesse (ht: Stop C e J u) :
    ∃ E dR : ℕ→ℝ, RateIs atTop σ E (-e) ∧ RateIs atTop σ dR (-e) ∧
      ∀ (r:ℝ), 0 ≤ r → r < 1/16 → ∀ᶠ k in atTop,
       ∃ (hu:u ≤ S k)(hk:S k+1 < k), ∀ (p:ℕ), ∃ (hi : ∀ i,Opened C (d i) k p)
          (hg: Opened C e k p),
       ∀ (N:ℕ) (hN:k < N) (ρ:ℝ) (z:I→ Cover) (x: ∀ i:I,C.label (d i)),
       Tuple C M η A k ρ z → quadrants C d k Gm x →
       let f:= Words C h d p N k x z hN.le hi
       let δ := (Nat.le_succ (S k)).trans hk.le
       let X₀ := (center C.S p (((ht.live.1.trans hu).trans δ).trans hN.le) 0)
       let Report := receipt C N p e h u k (ht.doors p) hg (hu.trans δ) hN.le f
       let Δ := discrepancy C h p N e u (ht.doors p) ((hu.trans δ).trans hN.le) f
       (∃ y q, Funds C h p N (S k) e J u (E k) (dR k) (weight C e k) f ht.live.1 hu (δ.trans hN.le) (ht.doors p) y q) ∧
       Δ=f-C.O N p (master C N p e h k hg hN.le Report) 0 ∧
       Interior (X₀.chamber 0) Δ ∧ X₀.rootTest (C.beta N p) Δ ≤
          (C.S.a k)^e*Real.exp (-r*C.S.scale k) := by
    obtain ⟨Q,h0,hQ⟩ := cylinder_cost C L h e J u ht.live ht.height ht.doors
    obtain ⟨E,dR,hE,hR,hu⟩:= expenses C hG L h d e J u Gm hGm η M A hη hM hA hpace ht.live ht.doors
    let s:= S; have hS:= port_height C hG (8*M) A (mul_pos (by norm_num) hM) (by linarith only [hA]) hpace
    refine ⟨E,dR,hE,hR,fun r hr₁ hr=>?_⟩
    have hpr : ∀ᶠ k in atTop, 2*(stakes C J u/weight C e k) + Q*(E k/gainChart C.path (S k) u) ≤
       C.S.a k^e*Real.exp (-r*C.S.scale k):= by
       have he:= RateIs.const (c:=stakes C J u) C.S.divergent (show 0<stakes C J u from Real.exp_pos _)
       have hx:= hw e
       have hδ:= hE.div (gain_toward C u hS)
       have hW:= ((RateIs.const C.S.divergent zero_lt_two).mul (he.div hx)).pays C.S.divergent
       have hp:= (RateIs.overtakes (((normal_height C).mesh.power e).mul (RateIs.exp (-r) C.S.divergent))
         ((hW.addMax ((RateLE.const Q C.S.divergent).mul (hδ.pays C.S.divergent)) C.S.divergent)) C.S.divergent
         (max_lt_iff.mpr ⟨by linarith only [hr],by linarith only [hr]⟩)).mono (fun i h=> h.le)
       exact hp
    obtain ⟨n,hn⟩:= eventually_atTop.mp (near_center C J e h)
    filter_upwards [hu,hpr,open_late C hG e,eventually_ge_atTop n] with k hu hp ho hx
    obtain ⟨hu,hk,hJobs⟩:= hu
    refine ⟨hu,hk,fun p=>?_⟩
    obtain ⟨hi,hJob⟩:= hJobs p
    refine ⟨hi,ho p,fun N hN ρ z x HT Hq=>?_⟩
    intro f δ X₀ Report Δ
    obtain ⟨y,q,hfund⟩ := hJob N hN ρ z x HT Hq
    have hB:= dress_inverse C N p e h k (ho p) hN.le (topReport C N p e h u (ht.doors p) ((hu.trans δ).trans hN.le) f)
    have heq : Δ=f-C.O N p (master C N p e h k (ho p) hN.le Report) 0:=by unfold Δ discrepancy Report receipt; rw [hB]
    obtain ⟨hu',hv⟩:= Funds.pay C h p N (S k) e J u hfund h0 (fun y=> ⟨hn N (hx.trans hN.le) (ht.live.1.trans ((hu.trans δ).trans hN.le)) p 0 (by rw [latzero]; simp [(C.S.a_pos _).le]) y, hQ N p ((hu.trans δ).trans_lt hN) y⟩)
    exact ⟨⟨y,q,hfund⟩,heq,hu',le_trans hv hp⟩
where
 hw e := (show RateIs atTop σ (weight C e) (e+1/16:ℝ) from RateIs.exp _ C.S.divergent)
end YM.RG16.Literal
