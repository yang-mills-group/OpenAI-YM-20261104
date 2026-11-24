import YM.OPE.Loom.Request
/-! # Root geometry scaled from the primary captures. At any fixed seams -/
set_option autoImplicit false
noncomputable section
open Filter Function Set MeasureTheory
open scoped Topology BigOperators Classical
namespace YM.OPE.Loom
open Lattice RG Wilson MergeProof Accent Ribbons Source Overlay Bid ManyCopies Next.Rank Next.UVStress PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
open Push Marker Cells Extraction
variable {G:Gauge} {C:Family G}{f:Extraction.Order}{T:Table C.book}{F:Spec.Final C f T}
local notation "Y" => C.path.levels
local notation "X" => C.path.levels.clock.hatBeta
local notation "S" => C.S
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "ζ" => fly C.path.levels
set_option quotPrecheck false
variable {𝓛:Filter (ℕ×ℕ)} [𝓛.NeBot] {B:Frame.Scheme F} (L:Origins B 𝓛) {W r D}(A:Sharper C W r D)
variable {I J:Type}[Fintype J] [DecidableEq J]{t d m K:ℕ}(s:J→ T.Tag) {φ:Filter I} {T' v: I→ℝ} {k j:I→ℕ} {y a:ℝ}
local notation "z" => (fun i=> (s i).1)
local notation "γ" d => (fun i=> (v i)^(d:ℕ))
variable (b : J) (h:Height C.S φ T' k y)(g:Height C.S φ T' j y) (hT:Tendsto T' φ atTop)
structure Route (C:Family G)(v:ℝ) (b:J) (x:J→ Cover) (t k:ℕ) : Prop where
   origin : x b=0
   radius : ∀ i,‖C.S.gridPoint k (x i)‖ ≤ v*t
   gaps : ∀ i l,i ≠ l → 4*v ≤ ‖C.S.gridPoint k (x i) - C.S.gridPoint k (x l)‖
   clean : Screen (C.S.gridPoint k ∘ x)
variable (H :∀ᶠ i in φ,k i+1 < j i ∧ Gate (α:=J) C r t (k i) (j i) m (v i))

-- demand unified semantics, supports moving representatives on the same label contractions.
structure Eyes (k':ℕ) (w:J→ℝ) : Prop where
    all (i:J): 0<w i ∧ ∃ u:C.label (s i).1, T.project _ u=(s i).2 ∧
       ∃ g:ℕ×ℕ→ C.label (s i).1, Tendsto g 𝓛 (𝓝 u) ∧ ∀ᶠ l in 𝓛,w i*Spindle.paid C (s i).1 k' l.1 l.2 (g l) ≤ fly (G:=G) C.path.levels (s i).1 k'
-- Moving continuum reports. Need orientation control & interpolation to even apply off-grid.
structure Desks (F:Spec.Final C f T) (φ:Filter I)(T' v : I→ℝ)(B:Frame.Scheme F)(s:J→T.Tag)(b:J)(j:I→ℕ)(a:ℝ)(m d t:ℕ) : Prop where
    keeps : ∃ (u : I→ℝ) (y': Frame.Row B.rings→ I→ℝ), Bill φ T' u (fun i=> (v i)^d/(v i)^Frame.load s) ∧
       (∀ p∈ Frame.limits B.rings d,Bill φ T' (y' p) (fun i=> (v i)^p.1/(v i)^Frame.load s)) ∧
       ∀ᶠ i in φ, ∀ x, Route C (v i) b x t (j i) → ∃ q:T.Field d,
           (∀ p∈ Frame.limits B.rings d, ‖B.representation.coord p d q‖ ≤ y' p i) ∧ Meets F s (C.S.gridPoint (j i) ∘ x) q a (u i) m
variable (hx:Tendsto v φ (𝓝[>]0))(hv:Bi φ T' (C.S.a ∘ j) v)(hb:Bi φ T' (C.S.a ∘ k) v)(hc:0<t)(hQ:K≥C.ref d)(ht:Stock.Tabs.opens C.path.levels 1 m K)
include s L h H g A hT hx hv hb hc hQ ht b
set_option maxHeartbeats 800000 in
theorem survey (H':Org.Grill C f) : Desks F φ T' v B s b j a m d t:=by -- req positive a? not using
    obtain ⟨w,hw,hW⟩:= onload B L hT g (z) (fun l=>(s l).2); obtain ⟨y,hY,hZ⟩:= L.bounds d
    have hU:∀ᶠ i in φ,∀ l,0 < w i l:= hW.mono fun i hi l=> (hi l).1
    let x i:= purse C (w i) (j i) (k i) t
    let e i:=2*ebb C d (k i) (x i); let p i:= bid C d K (k i) (x i); let z₀ i:=2*(stakes C m K/p i); let f' (p:Frame.Row B.rings) i:= e i*y (k i)*(C.S.a (k i)^p.1/C.S.a (k i)^d); let n:(ℕ):= Fintype.card J; have hn:0<n:= Fintype.card_pos_iff.mpr ⟨b⟩; have hp:∀ᶠ i in φ,0<x i:=by
       filter_upwards [hU] with i hi; have he j:0<δ j:= Real.rpow_pos_of_pos (zero_lt_one.trans ((Y).fits.delayed _)) _; have hh j:0<η j:= inv_pos.mpr (zero_lt_one.trans ((Y).fits.delayed _)); exact cashIn_pos _ _ (he _) hn (fun l=> price_pos (div_pos (mul_pos (he _) (mul_pos (hh _) (hi l))) (by norm_num)))
    have hv': ∀ᶠ i in φ,0<v i:= H.mono (fun i hi=>hi.2.pos)
    let w'(l:J) i:= (v i)^(s l).1; have he : Bi φ T' x (fun i=>∏ l,w' l i):= by
       apply Bi.prod hT; intro l _
       have hK : Bi φ T' (C.S.a ∘ j) (fun i=> C.S.a (k i+1)) := hv.trans (hb.symm.trans (shift_mesh hT h A.tabs).symm); have hh : Bi φ T' (fun i=>w i l) (w' l) := (hw l).trans (Bi.power hv hT ((s l).1))
       have hh' : Bi φ T' (fun i=> δ (j i)*(η (j i)*w i l)/8) (w' l):= by
          simp_rw [div_eq_mul_inv]; simpa only [one_mul,mul_one] using Bi.mul (Bi.mul (renal_coins hT g) (Bi.mul (near_coins hT g) hh)) (Bi.const ((8:ℝ)⁻¹) (by norm_num) hT)
       have hu:= price_coin hT (h.step (Y).fits.mesh) hK hh'; simpa only [one_mul] using! Bi.mul (license_polynomial hT (h.step (Y).fits.mesh) t A hn) hu
    let c i:=((v i)^Frame.load s)⁻¹; have hc₀:∀ᶠ i in φ,0<c i:=hv'.mono fun i hi=>inv_pos.mpr (pow_pos hi _); have hz:Bill φ T' (fun i=>(x i)⁻¹) c:= by
       have hEq : (fun i=>∏ l,w' l i)=(fun i=>(v i)^Frame.load s):= funext fun i=> by unfold w' Frame.load sigma; rw [Finset.prod_pow_eq_pow_sum]; rfl
       rw [hEq] at he; exact Bill.inverse he.down (hv'.mono fun i hi=> (pow_pos hi _).ne')
    have he': Bill φ T' e (fun i=>c i*C.S.a (k i)^d) := Cheap.times (Bill.const _ hT) (ebb_cost A d hT h hz)
    refine ⟨z₀,f',?_ ,fun p hp=>?_ ,?_⟩ -- construct syntax `Desks.keeps` via constructor? automatic multi
    · refine Bill.trans (Cheap.times (Bill.const (2*stakes C m K) hT) (bprice A d K hQ hT h hc₀ hz hp)|>.congr ?_ (EventuallyEq.refl ..)) ((Bill.mul (Bill.same φ T' c) (Bi.up (hb.power hT d))).congr (EventuallyEq.refl ..) (Eventually.of_forall fun i=> ?_))
      · filter_upwards with i; unfold z₀ p; ring
      change c i*(v i)^d=(v i)^d/(v i)^Frame.load s; rw [div_eq_mul_inv,mul_comm]
    · have hh := hY.up.of_tendsto h.grows; have ht := (he'.mul (Bill.enlarge hh (cheap_by_ratio hT h.pace))).mul (Bill.same φ T' (fun i=> C.S.a (k i)^p.1/C.S.a (k i)^d)); refine Bill.trans (ht.congr (EventuallyEq.refl ..) ?_) ((Bill.mul (Bill.same φ T' c) (hb.power hT p.1|>.up)).congr (EventuallyEq.refl ..) (Eventually.of_forall fun i=>?_))
      · filter_upwards with i; have ht:= C.S.a_pos (k i); change c i * _ * 1 * _ = c i*_ ; field_simp; rfl
      change c i*(v i)^p.1 = (v i)^p.1/(v i)^Frame.load s; rw [div_eq_mul_inv,mul_comm]
    have hξ : Tendsto (fun i=>8*(v i*t)) φ (𝓝 0) := by simpa using! (((hx.mono_right nhdsWithin_le_nhds).mul_const (t:ℝ)).const_mul (8:ℝ))
    filter_upwards [hW,H, h.grows.eventually (fits (C:=C) (lensScope C d) m), h.grows.eventually_ge_atTop K, h.grows.eventually hZ, eventually_all.mpr (fun l:J=>g.grows.eventually_ge_atTop (C.ref (s l).1)),hξ.eventually (ge_mem_nhds (C.S.a_pos m))] with i hi hg hξ0 hP hY hR ha u hy
    choose a' u' hu v' hV hh using hi; let w'(l:J):C.book.Token:= ⟨(s l).1,u' l⟩
    obtain ⟨p',hp'⟩ := viable F A (w i) w' v' b (show RootMark C t (k i) (j i) m K d (v i) r w' u b from ⟨hg.2,hg.1,hy.origin,hy.radius,hy.gaps,fun l=> le_trans (mul_le_mul_of_nonneg_left (hy.radius l) (by norm_num)) ha, ht,hP,hc,hQ,hR,hξ0⟩) a' hh L.extraction
    have he : T.classTokens ∘ w' = s:= funext fun l=> congr_arg (fun v:T.Field ((s l).1)=> (⟨(s l).1,v⟩: T.Tag)) (hu l)
    refine ⟨T.project _ p', fun l hl=>?_, proposes L s w' H' he p' v' hV hy.clean (by have h₁:=ht.1; have h₂:=hg.1; omega) hp'⟩
    obtain ⟨π,y',hh,hπ,hp,hχ⟩:=hp'.buys; exact hY.2 _ hh hπ _ _ _ hp (hχ.mono fun _ hh=> hh.1) _ hl
end YM.OPE.Loom
