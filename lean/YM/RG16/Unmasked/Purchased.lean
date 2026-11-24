import YM.RG16.Unmasked.Rates
/-!
# Assemble physical matched product receipts (before precision computation)

ONE root, literal separated fields, paid by full rep. Life for all k
sufficiently fine; keep price on many copies while comparison part only on
one receipt R. This can accept labels growing with k,costing rates in any
negotiated finite power of Λ or even coupling^(-O(1)). The shape is external
relative to the m grid and the labels in `master` in coupling coordinates.
The Π frame is representation-INVARIANT at finite cutoff. Choose capture stage
immediately before ≤ constants. Do not use the budgets in this file for
local Taylor precision -- they are bought on the SPATIAL scale with possibly
larger than exp(-log(g)*α) effects. The next estimate discounts them only
against discrepancy decaying in spatial scale.
-/
noncomputable section
namespace YM.RG16.Literal
open Function Set Filter MeasureTheory OPE Lattice Wilson RG Next.Rank Source Overlay Bid Push.GridApprox
open MergeProof Ribbons Accent ManyCopies Cells Extra.Histories
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
open scoped Topology Matrix.Norms.Frobenius Classical BigOperators ContDiff
set_option autoImplicit false
set_option quotPrecheck false
variable {G : Gauge} (C: Family G) (hG:G.Simple){W r D} (L:Package C W r D)
local notation "P" => C.path.levels
local notation "α" => renal C.path.levels
local notation "κ" => fly C.path.levels
local notation "σ" => C.S.scale
local notation "Θ" => near C.path.levels
local notation "β" => C.path.levels.clock.hatBeta
local notation "τ" => bling C.path.levels
local notation "F" => C.labels.level
open Trace.Physical.GermGraph

variable (h:C.Makes) {I : Type} [Fintype I][DecidableEq I] [Nonempty I] (d : I→ℕ)(p N b k e J u:ℕ)
  (Gm : ℕ→ℝ) (hGm : RateIs atTop C.S.scale Gm 0)

section
/-- input quote -- full reference portion along trajectory --- may grow. -/
def quadrants (x:∀ i:I,C.label (d i)) : Prop := ∀ i, (F (d i)).coeffSize (x i) ≤ Gm k

def Words (x:∀ i:I,C.label (d i)) (z:I→ Cover) (hk:k≤N) (hi:∀ i,Opened C (d i) k p) :=
    fun U=>∏ i,C.O N p (master C N p (d i) h k (hi i) hk (x i)) ((C.S.toDepth hk p).embed (snap C k p z i)) U

-- payoff at b. Contains same Z and Q, no high-order assumptions. matcost is
-- in the true u page, not cap price, include cost at the latter for replication use.
structure Funds (E dR w:ℝ) (f:Cut C N p) (hj:J ≤ u)(hu:u ≤ b)(hi:b ≤ N)
    (hh:Opened C e u p) (z:C.label e) (q: store C e p b) : Prop where
   life : reads e N p b q dR
   capZ : Next.UVStress.quota C e b N p z ≤ 2*E
   wide : Fleet C N p e b J f (hj.trans (hu.trans hi))
        (march (fun _ : Site (C.side J p) => w) (near C.path.levels) u b) q hi
   accounts : credit C N p e f b hi= value (C:=C) e N p b q
   inview : Interior ((center C.S p (hj.trans (hu.trans hi)) 0).chamber 0) (f-C.O N p z 0)
   works (i:ℕ)(hu:u ≤ i)(hp:i≤b): Booked C N p e f i (hp.trans hi)
   packing : (center C.S p (hj.trans (hu.trans hi)) 0).rootTest (C.beta N p) (f-C.O N p z 0) ≤ 2*(stakes C J u/w)
   currency : mCost C e N p u (topReport C N p e h u hh (hu.trans hi) f - (C.factory e N p).terminal.symm z) ≤ E/gainChart C.path b u
end

variable (η M A:ℝ) (hη:0<η)(hM:0<M)(hA:20<A)
  (hpace : ∀ i,((C.S.block i).val:ℝ) ≤ Real.log (Lambda C.path.levels i))
local notation "S" => port C (8*M) A (mul_pos (by norm_num) hM)
include hG hGm hη hA hpace L
set_option maxHeartbeats 1500000 in
/-- Price on all jobs. Growth/time and packing budgets export for later
entry estimates. The Θ mark budget buys dispatcher unification for ALL N>k,
not an eventual statement in period after cutoff. -/
theorem expenses (ht:Stock.Tabs.opens C.path.levels 1 J u)(ho:∀ p,Opened C e u p) :
    ∃ E dR : ℕ→ℝ, RateIs atTop σ E (-e) ∧ RateIs atTop σ dR (-e) ∧ ∀ᶠ k in atTop,
       ∃ (hu:u≤S k)(hk:S k+1 < k), ∀ (p:ℕ), ∃ hi : (∀ i,Opened C (d i) k p),
       ∀ (N:ℕ) (hN:k < N) (ρ:ℝ) (z:I→ Cover) (x: ∀ i:I,C.label (d i)),
       Tuple C M η A k ρ z → quadrants C d k Gm x →
       ∃ y q, Funds C h p N (S k) e J u (E k) (dR k) (weight C e k)
          (Words C h d p N k x z hN.le hi) ht.1 hu ((Nat.le_succ _).trans (hk.le.trans hN.le)) (ho p) y q := by
    let s:= S; have hS := port_height C hG (8*M) A (mul_pos (by norm_num) hM) (by linarith only [hA]) hpace
    let n:= Fintype.card I; have hn : 0<n:= Fintype.card_pos
    obtain ⟨y,hY,hz,hy⟩:= halls hG L.halos n hn
    let T (i:I) (k:ℕ):=2*((2*β k)^ (degree (F (d i)))*Gm k)
    let a' i (k:ℕ):= (κ (d i) k)/T i k
    have hc:= height0 (hut C hG) (normal_height C)
    have hw:= RateIs.const (c:=2) C.S.divergent zero_lt_two
    have hx(i:I):RateIs atTop σ (a' i) 0:=
        ((flyRate hG (normal_height C) (d i)).div (hw.mul ((((hw.mul hc).power (degree (F (d i)))).mul hGm)))).swap (by ring)
    have he (k:ℕ) (hk:∀ i: I,C.ref (d i) ≤ k)(ht:0<Gm k): ∀ i,0 < a' i k := fun i=>div_pos (L.system.grows _ _ (hk i))
       (by have hh := (P).fits.delayed k; unfold T; positivity)
    let Z k:= ManyCopies.initial C.path α Θ (s k) k (y k) (∏ i,a' i k) n
    have hu : RateIs atTop σ Z 0:= (Height.gathered hS (normal_height C) C.S.divergent (height0 hY (normal_height C)) (RateIs.prod («S»:=Finset.univ) (fun i _=> hx i) C.S.divergent) hG n).swap (by simp)
    let E i:=terminalCost C e (s i) (Z i)
    let p' i:= (C.S.a (s i+1))^e*(τ (s i)*(4*(1/Z i)))
    have hE: RateIs atTop σ E (-e):= (key_cost hS C.S.divergent hu hG e).swap (by ring)
    have hm:= hS.step (P).fits.mesh
    have hu':= height0 (banket C hG) hS
    have hX: RateIs atTop σ p' (-e):= ((hm.mesh.power e).mul (hu'.mul ((RateIs.const (c:=4) C.S.divergent (by norm_num)).mul ((RateIs.const C.S.divergent one_pos).div hu)))).swap (by ring)
    obtain ⟨χ,hχ⟩:= L.productCuts.mother
    have hF:= (height0 (briar C hG L.accounting) hm|>.power 2).add (RateIs.const C.S.divergent one_pos) C.S.divergent |>.mul hm.mesh
    let f:= L.system
    obtain ⟨t,tp⟩:= eventually_atTop.mp ((near_center C J e h).and (eventually_all.mpr (fun i:I=> near_center C J (d i) h)))
    have hr0 := rooted_layout (I:=I) C hG M η A hM hη hA  -- arg order
    refine ⟨E,p',hE,hX,?_⟩
    have hOpen : ∀ᶠ k in atTop,∀ i:I,∀ p:ℕ,Opened C (d i) k p:= eventually_all.mpr fun i=> open_late C hG (d i)
    filter_upwards [hr0,hOpen,late_march C hG L u e (ho 0|>.post) hS hE hu,
      hS.grows.eventually_ge_atTop u,hS.grows.eventually (plenty P J (lensScope C e)), hGm.pos,
      eventually_ge_atTop t,hu.pos,
      (RateIs.const C.S.divergent (C.S.a_pos J)).overtakes (hF.pays C.S.divergent) C.S.divergent (by simp)] with k hp hO hW hs hr htM hk hu hv
    have hab : s k+1 < k:= hp.1
    let i0 : I:= Classical.arbitrary I
    refine ⟨hs,hab,fun p=>⟨fun i=>hO i p,fun N hN ρ z x hb hq=>?_⟩⟩
    obtain ⟨hcU,hV,hφ,hpose⟩:= hp.2 ρ z p hb
    let U i:= snap C k p z i
    let r':= C.S.toDepth (((ht.1).trans hs).trans ((s k)|>.le_succ)) p
    have hJ: J ≤ s k+1:= ht.1.trans (hs.trans ((s k)|>.le_succ))
    have hx' : (((P).budget (s k+1)).B^2+1:ℕ) ≤ r'.count.val:=by
       have he: (((P).budget (s k+1)).B:ℝ)^2+1 ≤ r'.count.val:= le_of_mul_le_mul_right (hv.le.trans_eq ((C.S.embeds_scale r').symm.trans (mul_comm ..))) (C.S.a_pos _)
       exact_mod_cast he
    let v (i:I):= master C N p (d i) h k (hO i p) hN.le (x i); let u' (i:I):=C.O N p (v i) ((C.S.toDepth hN.le p).embed (U i))
    have hxF i:T i k> 0:= by have hh:= (P).fits.delayed k; unfold T; positivity
    have ht'(i): a' i k*Spindle.paid C (d i) k N p (v i)≤ κ (d i) k:=by calc
         _ ≤ a' i k*T i k:= by
            refine mul_le_mul_of_nonneg_left ((master_price C h N p (d i) k (hO i p) hN.le (x i)).trans ?_) (he k (fun i=> (hO i p).post) htM i).le
            unfold T; apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2); refine mul_le_mul_of_nonneg_left (hq i) ?_; have h₀:= (P).fits.delayed k; positivity
         _ = _ := div_mul_cancel₀ _ (hxF i).ne'
    have hT:= tp N (hk.trans hN.le)
    have h_N: J ≤ N:= hJ.trans (hab.le.trans hN.le)
    have hbe(z:C.label e): Interior ((center C.S p h_N 0).chamber 0) (C.O N p z 0):= hT.1 h_N p 0 (by rw [latzero]; simp [(C.S.a_pos _).le]) z
    have hpos(i:I): Interior ((center C.S p h_N 0).chamber 0) (u' i):= by
       refine hT.2 i _ _ _ ?_ _; rw [C.S.embeds_place]; exact le_trans (hV i) (C.S.strictAnti.antitone hJ)
    obtain ⟨b,hbZ,hInterior,hTest,⟨q,hqU,hqr,hreads⟩,hp,hx⟩:= joins_true_headroom C N (s k) p e J u i0 (weight C e k) (fun i=> a' i k) (snap C k p z) ht.1 hs hN hab.le d v h L.system L.literal (hχ e) L.tabs ht (ho p).post (fun i=> (hO i p).post) ht' (he k (fun i=> (hO i p).post) htM) hr hφ hx' hpose (hY.pos k) (hz k) (fun i hi hx=> hy k i hx.le) u' (fun _=>rfl) hpos hbe hu le_rfl (ho p) (weight_pos C e k) hW.1 (le_refl (E k)) hW.2
    exact ⟨b,q,hreads,hbZ,hqU,hqr,hInterior,hp,hTest,hx⟩
end YM.RG16.Literal
