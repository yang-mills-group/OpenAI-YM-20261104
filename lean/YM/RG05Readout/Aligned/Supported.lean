import YM.RG05Readout.Aligned.Purse
/-!
# One path from actual tagged cutoff density to the matcher

Intermediate aligned version, WM spatial scales with REAL published
supports. `IssueAt` uniform for the whole given finite alphabet (and
ultimately deployed at *the same* inputs through the perturbative
hypotheses). The finite test inequalities quantify in C including **period**
while computing a capture.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Aligned
open Filter Topology Set Function Lattice RG Extraction Wilson Source OPE
open MergeProof Accent Ribbons ManyCopies PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
open Next.Rank Bid Cells
open scoped Topology BigOperators Classical
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book} {η:ℕ} {φ:Filter (ℕ×ℕ)}
    (hG:G.Simple) (hC:C.Makes) {W D r}(L:Package C W r D) {J k d N j p m : ℕ}
    {I Y:Type}[Fintype I] {l:Filter Y} {T t:Y→ℝ}{s n:Y→ℕ}

/-- Actual cluster product. Offsets are at the observation mesh j,
center at origin, exact one column recipe used regardless of x. This uses
`location`, not fractional preimage/smear -- see `Columns` doc. -/
def product (N p j:ℕ) (x:I→ Cover) (d:I→ℕ) (v:∀ i,C.label (d i)) :
    Config G (C.side N p) →ℂ :=
    fun U=>∏ i, C.O N p (masterRef hC (d i) j N p (v i))
        (Cells.location C.S j N p (x i)) U

local notation "ν"=> near C.path.levels
local notation "T'"=> fly C.path.levels
local notation "X"=> bling C.path.levels

open Extra.Histories
variable {Q :Worth} {D :∀ N p m:ℕ, m<N→ GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}

/-- Labelled reports, existential in labelled choices. The actual *value*
report is `payload`. Carries the calibration receipt down to the fixed
reference. -/
structure Journey (hC:C.Makes)(V':Worth) (D :∀ N p m:ℕ, m<N→ GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m))
    (d J k m j N p:ℕ) (a:I→ℕ)(x:I→ Cover)(v:∀ i,C.label (a i))(y E:ℝ) where
    dictum : Music (C.labels.level d) C.path N p
    issued : Committed C N p d V' (waybill C.path.levels) D dictum
    mark : Coefficient (C.labels.level d) (C.side m p)
    record : ∀ i:ℕ,Relay.Solo (C.labels.level d) C.path p i
    traceMatch : Pickup C dictum (waybill C.path.levels) D issued m mark y E record
    ancestral : J ≤ m
    certified : Captured C N p J m d traceMatch.top ancestral (product hC N p j x a v)
       (march (fun _:Site (C.side J p)=> markRadius C d j) (near C.path.levels) k m)
       mark y

namespace Journey
variable {a:I→ℕ}{x:I→ Cover}{v:∀ i,C.label (a i)} {w A:ℝ}
    (hoff: Journey hC Q D d J k m j N p a x v w A)

def payload: C.label d:= Pickup.coordinate hoff.dictum hoff.record j hC

/-- Exact terminal-issued physical label of this report. -/
lemma reads : masterRef hC d j N p (hoff.payload hC)=
    (hoff.record (C.ref d)|>.bar hoff.dictum 0).x:=by
    rw [payload, hoff.traceMatch.scale_back _ hC, hoff.traceMatch.ref_coordinate hC]
end Journey

/- columns uniform *costs* at WM -/
variable (a:I→ℕ) (b:I→ℝ)
set_option quotPrecheck false
local notation "B"=> C.path.levels

include hG L in
lemma room_for (hh:Height C.S l T n 1)(ht:Tendsto T l atTop)(J d:ℕ):∀ᶠ i in l,
       Push.GridApprox.room C.path.levels J (n i) (lensScope C d) ∧ ∀ (e:J ≤ (n i+1)) (p:ℕ), ((C.path.levels.budget (n i+1)).B^2+1:ℕ) ≤ (C.S.toDepth e p).count.val := by
    have h₁ : ∀ᶠ i in l, Push.GridApprox.room C.path.levels J (n i) (lensScope C d) := by
       -- fixed J
       have hz := ((RateIs.const (c:=30) ht (by norm_num)).mul hh.mesh).mul (height0 (note_reg (B)) hh)
       have he := (RateLE.const (2:ℝ) ht).mul ((RateLE.mul (hh.mesh.pays ht) (RateLE.const ((lensScope C d):ℝ) ht)).add (hz.pays ht|>.mono (by linarith only)) ht)
       exact (RateIs.const ht (C.S.a_pos J)).overtakes he ht (by linarith only)
    have hm:= hh.step C.path.levels.fits.mesh
    have he:=(RateIs.const ht (C.S.a_pos J)).overtakes (((((height0 (briar C hG L.accounting) hm).power 2).add (RateIs.const ht one_pos) ht).mul hm.mesh).pays ht) ht (by simp)
    filter_upwards [h₁,he] with i h hp
    refine ⟨h,fun z p=>?_⟩
    let v:= C.S.toDepth z p
    have hl: (((B).budget (n i+1)).B:ℝ)^2+1 ≤ v.count.val:= by
        apply le_of_mul_le_mul_right _ (C.S.a_pos (n i+1)); exact hp.le.trans_eq ((C.S.embeds_scale v).symm.trans (mul_comm ..))
    exact_mod_cast hl

-- record bound on any of the Journey choices returned across calls,
-- so continuum user can read this SAME path, not a fresh existential.
structure IssueAt (f:Extraction.Order) (L:Package C W r D) (a:I→ℕ) (b:I→ℝ)
    (d J k m j:ℕ)(y E:ℝ) : Prop where
    priced : 0 < E
    -- costing at eventual (N,p), strictly in Extraction order;
    -- construction is valid wherever the native inequalities / J room hold
    program x : Plot C k m j x → ∀ᶠ i:ℕ×ℕ in f.fuse, ∀ (v : ∀ j,C.label (a j)), (∀ j,(C.labels.level (a j)).coeffSize (v j) ≤ b j) →
       Nonempty (Journey hC W D d J k m j i.1 i.2 a x v y E) ∧
       ∀ H: Journey hC W D d J k m j i.1 i.2 a x v y E,
            Next.UVStress.quota C d m i.1 i.2 (masterRef hC d j i.1 i.2 (H.payload hC)) ≤ 2*E ∧
            Cards.PaidAt C.S i.1 i.2 J (C.beta i.1 i.2) (2*(stakes C J k / markRadius C d j))
              (product hC i.1 i.2 j x a v - C.O i.1 i.2 (masterRef hC d j i.1 i.2 (H.payload hC)) 0)

include L hG
lemma issue_at (f:Extraction.Order)(i₀:I)(hd:Stock.Tabs.opens C.path.levels 1 J k)
    (hβ:∀ i,0<b i) (hc:C.ref d ≤ k)
    (hh:Height C.S l T n 1) (hj:Height C.S l T s 1) (ht:Tendsto T l atTop) :
    ∃ y E:Y→ℝ, RateIs l T E (-d:ℝ) ∧ ∀ᶠ i in l, IssueAt hC f L a b d J k (n i) (s i) (y i) (E i) := by
     obtain ⟨χ,hχ⟩:= L.productCuts.mother
     have hcI : 0 < Fintype.card I:= Fintype.card_pos_iff.mpr ⟨i₀⟩
     obtain ⟨α,w,hw,hR,hs⟩:= arms hG L a b hh hj ht hβ hcI
     let Y i:= C.S.a (n i+1)^d*(X (n i)*(4*(1/w i)))
     let E i:= terminalCost C d (n i) (w i)
     have hE : RateIs l T E (-d:ℝ) := (key_cost hh ht hw hG d).swap (by ring)
     refine ⟨Y,E,hE,?_⟩
     filter_upwards [hE.pos, hw.pos, repayment hG L d hh hj ht hc hw hE,room_for hG L hh ht J d,eventually_all.mpr fun u:I=> hj.grows.eventually_ge_atTop (C.ref (a u))] with i hi hw hW hr hSr
     refine ⟨hi,fun x hx=> ?_⟩
     let m := n i; let j := s i; have hb:= hd.1.trans hx.first; have he:= m.le_succ.trans hx.last
     rw [Extraction.Order.fused, Extraction.Order.late]
     filter_upwards [f.per.cofinal.eventually hx.marsh] with p hp
     let p':=f.per p; let o:= wrap (C.side j p') ∘ x
     have hs': Next.Rank.Edition.Spaced (C.path.levels.budget j).B o ∧ ∀ u, loops C j p' (o u) (m+1)=0 ∧ C.S.place (o u) = C.S.gridPoint j (x u):= hp
     have hz:= f.mesh.cofinal
     filter_upwards [hz.eventually_gt_atTop j, hz.eventually (near_center C J d hC),eventually_all.mpr fun u:I=> hz.eventually (near_center C J (a u) hC)] with N hN hK hG
     let N':= f.mesh N
     intro v hy
     have hNp:j < N':= hN
     have hwp:= hW
     let z (u:I):= masterRef hC (a u) j N' p' (v u)
     let V:=product hC N' p' j x a v
     let U(u:I):=C.O N' p' (z u) ((C.S.toDepth hNp.le p').embed (o u))
     have hu : V=(fun T=>∏ i,U i T):=by unfold V product; simp only [Cells.location,dif_pos hNp.le]; rfl
     let hJ:=hb.trans (he.trans hNp.le)
     let Z:= center C.S p' hJ 0
     have HT: Continuous V:= hu.symm ▸ continuous_finsetProd _ (fun i _=> C.continuousO ..)
     have hc'(q:C.label d):Interior (Z.chamber 0) (C.O N' p' q 0):=hK hJ p' 0 (by rw [latzero]; simp [(C.S.a_pos J).le]) _
     have he' : Interior (Z.chamber 0) V:= by
        rw [hu]; refine Interior.combines U _ (fun u hu=> hG u hJ p' _ ?_ _)
        rw [C.S.embeds_place, (hs'.2 u).2]
        exact (hx.fit u).le.trans (C.S.strictAnti.antitone (hb.trans m.le_succ))
     let v' i := T' (a i) j/b i
     let w':= markRadius C d j
     have hw':0 < w':=Real.exp_pos _
     constructor
     · have hv(i):0<v' i:=div_pos (L.system.grows _ j (hSr i)) (hβ i)
       have H' : ∀ i, v' i*Spindle.paid C (a i) j N' p' (z i) ≤ T' (a i) j:=by
           intro i; unfold z; rw [spendMaster hC (hSr i) hNp.le]; exact (mul_le_mul_of_nonneg_left (hy i) (hv i|>.le)).trans_eq (div_mul_cancel₀ _ (hβ i).ne')
       obtain ⟨Q₀,hQ⟩:= RG05_cluster C N' m p' d J k i₀ w' v' o hd.1 hx.first hNp hx.last a z hC L.system L.literal (hχ d) hc hSr H' hv (fun i=> (hs'.2 i).1) (hr.2 (hb.trans m.le_succ) p') hs'.1
             (hR (s i)|>.1) (hR (s i)|>.2.1) (fun _ _ hj=> (hR (s i)).2.2 _ hj.le) U (fun _=>rfl) hw (le_of_eq (hs i)) hw' hwp.1
       obtain ⟨M,hM⟩:= committing (N:=N') (p:=p') L.system (d:=d) (hc.trans (hx.first.trans (he.trans hNp.le)))
       have hμ := hQ; rw [← hu] at hμ
       obtain ⟨t,he⟩:= picks hM hC (hc.trans hx.first) (he.trans hNp.le) hμ.style hμ.pays (2*Y i) (by linarith only [show (C.labels.level d).coeffSize Q₀.x ≤ Y i from hμ.finite]) (le_refl (E i))
       exact ⟨⟨M,hM,Q₀,t,he,hb,hμ⟩⟩
     intro H
     obtain ⟨hz,hA⟩:= Pickup.root_cost C N' m k p' d hC w' L.system L.tabs J hd V H.mark H.traceMatch hi hc (lt_of_le_of_lt he hNp) (hk:=hx.first) hr.1 hc' HT he' hw' hW.2 H.certified.encoded
     have hX : masterRef hC d j N' p' (H.payload hC)=(C.factory d N' p').terminal (H.record (C.ref d)).a:=
       (H.reads hC).trans (H.traceMatch.ref_coordinate hC)
     change Next.UVStress.quota C d m N' p' (masterRef hC d j N' p' (H.payload hC)) ≤ _ ∧ Cards.PaidAt _ N' p' _ _ _ (V- C.O N' p' (masterRef hC d j N' p' (H.payload hC)) 0)
     rw [hX]; exact ⟨hz,⟨hJ,Next.UVStress.minus he' (hc' _),hA⟩⟩

end YM.RG05Readout.Aligned
