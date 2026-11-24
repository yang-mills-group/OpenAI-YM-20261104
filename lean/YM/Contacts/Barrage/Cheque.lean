import YM.Contacts.Barrage.Drain
namespace YM.Contacts.Barrage
open Function Set Finset Filter RG Wilson Lattice Precision Exterior Push.AbsoluteSums Extra.Iteration
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F08
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{s η:ℝ≥0}{b c e:ℝ}{P: Patch}{B H:Bed}{m f L : Side}{n r k i j:ℕ}
namespace Reserve
open Origin Slope Ion Resetter Lumen Next.Free Extension.UV.Linear
variable (T:MapPrices)
def purse (i:ℕ): ℝ:= max 1 (T.Ω i)
lemma purse_pos (i):0<purse T i:=lt_of_lt_of_le zero_lt_one (le_max_left ..)
-- need pre-budget for rank 2 kernel and norm, also α
lemma kin_bill (i:ℕ) : ∃ Z≥(0:ℝ),∀ B:Bed, B.metric.strip (T.α i) (purse T i) → (krow B.metric).strip (T.α i) Z:= by
   obtain ⟨c,C,h⟩:=delta_budget 1 (T.α i); refine ⟨_,?_ , fun B hB=> strip_compose (T.alpha_pos i).le (strip_compose (T.alpha_pos i).le (strip_trans h) hB) h ⟩; have h:=purse_pos T i; positivity
variable {F X:bore G}
private lemma toned_axis {G:Gauge}{A:FreeResolvent.FaceRow} (h:Whole A)(v:ℕ)(hv:(krow A).strip (s:ℝ) b)(hb:0≤b)(m:Side) (hu:(2*(η:ℝ))≤s): Shadow (lower m) (kin G A v) (circ G m A v):= by
   by_cases hx: v=0; · subst v; exact fun i=> Fin.elim0 i
   letI: NeZero v:= ⟨hx⟩; obtain ⟨P,hP,hK⟩:= (kin_desc m A h hv hb hu v (G:=G)).owes -- rotate
   have he:P=circ G m A v:= funext fun x=> by symm; exact sub_eq_zero.mp (norm_le_zero_iff.mp (hK.bound x 0))
   rw [← he]; exact hP
lemma east (h:Blazing F B)(he: Rooted (terrain s _) (F 0 2) b)(hw:Whole B.metric): F 0 2= kin G B.metric 2:= by
   obtain ⟨s,z,hs,hz⟩:= k_capacity hw; lift s to ℝ≥0 using hs.le; have hZ : 0≤z:= Cost.nonneg (hz (coord 0) (coord 0)); have hl (m: Side):= kin_desc m B.metric hw hz hZ (η:=0) (by simp) 2 (G:=G);
   exact receives he (hl 1).ground (fun i=> ⟨printFeeds (heritage (fun a=> (h.frame.here a 0 2)) i), (h.pri i).poem 0 2, toned_axis hw 2 hz hZ i (η:=0) (by simp),circ_shape _⟩) (fun v=>funext fun i=> ((h.pri v).glow i).trans (circ_read ..).symm)
lemma sheet (G:Gauge)(i k:ℕ): ∃ Z≥(1:ℝ),∀ B:Bed, B.metric.strip (T.α i) (purse T i) → Rooted (bath (sight T i/2) k _) (kin G B.metric 2) Z:= by
   obtain ⟨C,hC,h⟩:= kin_bill T i; obtain ⟨G',hg,hG⟩:= show ∃ d:ℝ,0≤d ∧ ∀ B:Bed, B.metric.strip _ _ → Rooted (terrain (sight T i) _) (kin G B.metric 2) d from ⟨_,mul_nonneg (by positivity) (mul_nonneg (by positivity) hC),fun B hb=> (kin_desc (G:=G) 1 B.metric ⟨_,_,T.alpha_pos i,hb⟩ (s:=rentCheque T i) (h B hb) hC (η:=sight T i) (by have he:= (shelf_span T i).1; change _≤ T.α i; linarith only [he, NNReal.coe_nonneg (sight T i)]) 2).ground⟩
   have hx : sight T i/2 < sight T i:= div_lt_self (sight_pos ..) one_lt_two; exact ⟨_,le_max_left ..,fun B hb=> (expand_fee hx (hG B hb)).weaken (fun _=>le_rfl) (le_max_right ..)⟩
def share (T:MapPrices)(G:Gauge)(i k:ℕ) := (sheet T G i k).choose
lemma sharing (G:Gauge)(i k): 0<share T G i k:= zero_lt_one.trans_le (sheet ..|>.choose_spec.1) -- syntax
-- pre contraction. prices evaluated at stage j=(i+1) tier, v∈{j,j-1}
def frock (i:ℕ):= 5-i -- k ≤3 for i≥2
lemma censure (T:MapPrices)(G:Gauge)(j v k i:ℕ)(hg:k≥3)(hi:0 < i ) : ∃ Z:ℕ,∀ (s η:ℝ≥0)(L:Side),L.val≥Z→ Odd L.val → 0<s → (η:ℝ)*2 ≤ T.α j → ((2*(η:ℝ)/(L.val:ℝ))*(i+1))≤s →∀ (X:Field (Fin (i+1)) (Node (Dye G))) (R:Spine.voyage L) (b:ℝ), author (extract X)=X →Poem X →softRank (frock (i+1)) X→ Rooted (bath s k _) X b → (∀ (l:List Axis), l.length ≤3 → (advanceC L R l).strip (T.α j) (purse T j / (L.val:ℝ)^(1+l.length))) → Rooted (bath η k _) (lifts (Origin.bleed G R) X) (b * (Real.exp (-(Real.log L.val)/2) / (1+share T G v k))):= by
    let u:=rentCheque T j; let p:= purse T j; let y:=frock (i+1); have hp:0< p:=purse_pos ..; have hu : y ≤3 := by unfold y frock; omega
    obtain ⟨F,hF,H⟩:= prolonged u (rent_pos ..) (Dye G) (Dye G) i k y (hu.trans hg) p hp.le; let M:= share T G v k; obtain ⟨q,hq⟩:= pessimistic (b:=0) le_rfl (1:ℝ) (F*(1+M)) zero_lt_one; refine ⟨q,fun s η L h hL hs he hv X R b ha hX hS hx hw=> ?_⟩
    let l:ℝ:= L.val; have hl:1 ≤ l:= by unfold l; exact_mod_cast (show 1≤ L.val from L.property)
    have h':0<1+M:=by have hm:=sharing T G v k; unfold M; linarith
    have HH:= H L hL η s hs he hv (Origin.bleed G R) (fun u hi=> by rw [Origin.advance_bleed]; exact Origin.bleed_strip (G:=G) (s:=rentCheque T j) (hw u (hi.trans hu)) (by change 0≤ p/l^_; positivity)) X hX ha hS b hx
    refine HH.even.weaken (fun _=>le_rfl) ?_; rw [mul_comm b]; refine mul_le_mul_of_nonneg_right (le_trans (b:=F/l) ?_ ?_) hx.cash; swap; · exact (le_div_iff₀ h').2 (show F/l*(1+M) ≤ Real.exp _ from by rw [div_mul_eq_mul_div]; exact (hq L h).2)
    let n:=i+1+y; change F*l^4/l^n≤F/l; have hg: 5≤n:= by unfold n y frock; omega
    have he:l^5 ≤ l^n:= pow_le_pow_right₀ hl hg; apply le_trans (div_le_div_of_nonneg_left (by positivity) (by positivity) he); field_simp; exact le_rfl
def peak (G:Gauge)(j v k i:ℕ): ℕ:= if h:k≥3∧0 < i then (censure T G j v k i h.1 h.2).choose else 0
def planned (T:MapPrices)(G:Gauge)(j:ℕ) : ℕ:= Finset.sup (Iic j) (fun k=> Finset.sup (Iic j) (fun i=> max (peak T G j j k i) (peak T G j (j-1) k i))) + j
lemma occupied (G:Gauge)(hk:k≥3)(hn:k≤j)(he:0 < i )(hh:i≤j) (hp : v=j∨v=j-1): (censure T G j v k i hk he).choose ≤ planned T G j:= by
   have hz : _= (censure T G j v k i hk he).choose:= (show peak T G j v k i= _ from dif_pos ⟨hk,he⟩); rw [← hz]; refine le_trans (Finset.le_sup_of_le (Finset.mem_Iic.mpr hn) (Finset.le_sup_of_le (Finset.mem_Iic.mpr hh) (hp.elim ?_ ?_))) (Nat.le_add_right _ _); · intro h; rw [h]; exact le_max_left ..
   intro h; rw [h]; exact le_max_right ..
-- Thresholds for EXP→power transfers. Not proof using uniform strips for e.g. root sector. Static all finite
variable (G)
open Spark
variable (P:Patch)(K: KernelChoices)
def gate (T:MapPrices)(j:ℕ):= min (1:ℝ≥0) (min (sight T j) (sight T (j-1))) / 8
lemma gate_pos (j):0<gate T j:= div_pos (lt_min zero_lt_one (lt_min (sight_pos T _) (sight_pos T _))) (by positivity)
structure Span (j:ℕ)(t:ℝ≥0) (x:ℝ) (B:Bed) (V:Wheel G P K B) : Prop where
   wheel : V.V.strip t x
   tilt : (Origin.stretch P K G V.V).strip t x
   charge {H:Bed} (U:Wheel G P K H) (hm : H.metric.strip (T.α j) (purse T j)) (hh:∀ n,(H.metric.acts n)ᵀ= H.metric.acts n ∧ Gap (H.metric.acts n) (T.η j)) (b:ℝ)(hb:0≤b)(he : (portfolio B.metric H.metric).strip t b):
       (minusRows U.V V.V).strip t (x*b) ∧ (minusRows (Origin.stretch P K G U.V) (Origin.stretch P K G V.V)).strip t (x*b) -- One same ratio. direction flipped.
lemma wheel_bank (j:ℕ) : ∃ (t:ℝ≥0) (x:ℝ),0<t ∧ t≤gate T j ∧ 1≤x ∧ (P.Branches K G → ∀ B:Bed,B.metric.strip (T.α j) (purse T j) → (∀ n,(B.metric.acts n)ᵀ=B.metric.acts n ∧ Gap (B.metric.acts n) (T.η j)) → ∀ V:Wheel G P K B,Span G T P K j t x B V):= by
   by_cases hx:P.Branches K G; swap; · exact ⟨_,_,gate_pos T j,le_rfl,le_refl 1,fun h=> (hx h).elim⟩
   obtain ⟨t,x,ht,hx',hh⟩:=ceilCapacity P G K hx (rent_pos T j) (purse_pos T j).le (T.eta_pos j); let L:=min t (gate T j); have hl:L≤gate T j:= min_le_right ..; have hw:0 < L:=lt_min ht (gate_pos T j);
   let z:ℝ:= (Fintype.card (Cellar G P.L):ℝ)*(x*(‖K.penalty‖*(probe_ready P L L.property).choose)); let W:= max (max (1:ℝ) x) (max z (max (payDiff P G x) (tiltDiff P K G L x)))
   have he (B:Bed)(V:Wheel G P K B)(h:B.metric.strip (T.α j) (purse T j))(hv : ∀ n,(B.metric.acts n)ᵀ=B.metric.acts n ∧ Gap (B.metric.acts n) (T.η j)): V.V.strip L x:= by
      obtain ⟨U,hU,hP⟩:= hh B h hv; have hv: Cabinet (brick G P K.penalty B) U:= hP; have hx : V.V=U:= by
         apply bank_injective V.strip.safe (Row.rights _ _ hU t.property); intro n; conv=> lhs; skip
         have hu :∀ (α:Type) (_: Fintype α) (_:DecidableEq α) (A B C:Matrix α α ℝ), B*A=1→A*C=1→ B=C:= fun _ _ _ a b c h hp=>by rw [← mul_one b, ←hp, ← mul_assoc,h,one_mul]
         exact hu _ _ _ _ _ _ (V.governed.l n) (hv.r n)
      rw [hx]; exact strip_mono hU (NNReal.coe_le_coe.mpr (min_le_left ..)) le_rfl
   refine ⟨L,W,hw,hl,(le_max_left ..).trans (le_max_left ..), fun _ B hB hV V=> ?_⟩; refine ⟨strip_mono (he B V hB hV) le_rfl ((le_max_right ..).trans (le_max_left ..)), strip_mono (widen P K G V.V (he B V hB hV) hx') le_rfl (le_trans (b:= max z _) (le_max_left ..) (le_max_right ..)), ?_⟩
   intro H U hm hh b hb hw'; have hx :Whole B.metric:= ⟨_,_, T.alpha_pos j,hB⟩; have hU:Whole H.metric:= ⟨_,_,T.alpha_pos j,hm⟩; have hx1 := he B V hB hV; have hx2:=he H U hm hh; rw [mul_comm W b]; exact ⟨strip_mono (charge_sqr _ hx hU V.governed U.governed hx1 hx2 hw' hw hb hx'|>.1) le_rfl (mul_le_mul_of_nonneg_left ((le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..))) hb),strip_mono (radii hx hU V.governed U.governed hx1 hx2 hw' hw hb hx') le_rfl (mul_le_mul_of_nonneg_left ((le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..))) hb)⟩
end Reserve
end
end YM.Contacts.Barrage
