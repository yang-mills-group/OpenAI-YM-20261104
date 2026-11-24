import YM.RG05Readout.Planes.Mesa
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Planes
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {b k l:ℕ}{Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
open Pulse Extraction Extraction.Lease
open Push.RelayDifference
variable {D:Address.Rail C}

variable {f: Extraction.Order}

/-! A transcription at common origin: affordable → vetted literal against calibrated matrices, absorb a finite bank then same at ALL higher SBP orders on-demand. For low-weight planes repaint them further. -/
open Bay Chalice

/-!
# Cone receipts.Boolean Ward.
 Weighted REAL ancestry maps. Projection kernel not discarded here. This proves linear inverse attenuation for surviving low-engineering weights and propagation bound for the rest, not lower/separated aperture budget by assumption. Using m≫ as required from Husk.C. -/
local notation "Z!"=> C.path.levels
local notation "χ"=> Address.clear C
local notation "S"=> Palette C d
local notation "J"=> Mark C d
local notation "ξ"=> C.S.block
local notation "L"=> C.S.block i
local notation "p!"=> BudgetPoint
variable {e:ℕ}{s t α A E:ℝ}
local notation "ΠΩ"=> Address.clear C d e
local notation "T"=> LinearMap.id (R:=ℂ) (M:=S) - Address.clear C d e
local notation "Ω"=> amplify d C L
/-!
# Cone with real engineering cash per level.
 Comparison of actual observation inverse normalized vectors through array. Prove equivalence in complement before projecting any kernel.N.C. Uses finite-dimensional plane algebra adapted from OPE/Columns/Plane. -/
-- abstracts measured clarity.Classic. tangent leakage. Peak normalized by subtree ledger.
structure Costume (i d e:ℕ) (C:Family G)(U: Palette C d≃ₗ[ℂ]Palette C d)(A:ℝ):Prop where
   positive: 1 ≤ A
   hat (x): size (amplify d C (C.S.block i) x) ≤ A*size (U x)
   body (x): size (U x) ≤ A*size (amplify d C (C.S.block i) x)
   sides x: Address.clear C d e x=0 → size (Address.clear C d e (U x))≤ tolerance C i * size x
local notation "M!"=> tolerance C i
variable {U:Palette C d ≃ₗ[ℂ] Palette C d}
include h
lemma Costume.earned {u:Address.Emblems C d}{P: Sight C d p}(hx:Spine D B h b p d N P u)(hw:Awake D B b d)(ht:b ≤ i)(hn:i < N) : Costume i d e C (u i) (powerFare B d i):=by
     obtain ⟨⟨k,d',s,he,hM,hQ⟩,hV⟩:= adhered h hw hx ht hn
     have hK:1 ≤ powerFare B d i:=by unfold powerFare; nlinarith [le_max_left 1 (B d i)]
     exact ⟨hK,fun x=>(hV x).2,fun x=>(hV x).1,fun x hx=>le_trans (leaked hQ x hx) (mul_le_mul_of_nonneg_right hM (size_ge x))⟩
omit h
variable (hc:Costume i d e C U A)
include hc
abbrev sufficient (C:Family G)(i:ℕ)(A:ℝ):Prop:=10*A^3 * tolerance C i ≤ 1/2
omit hc in
lemma dwindles (C:Family G)(i:ℕ) : 0 ≤ tolerance C i:= add_nonneg (Copper.lit _).le (mul_nonneg (zero_le_one.trans (lamp_nn (C:=C) _)) (Doors.rate_pos _|>.le)) -- omit
lemma Costume.stays (y:S) (he:ΠΩ y=0)(ht:sufficient C i A): size (Ω y) ≤ 2*A*size ((T) (U y)):=by
    let t:= Ω y; let q:= size ((T) (U y)); have hp:=hc.hat y; have hx:=hc.sides y he; let w:=size t
    have hf : size (U y)≤ q + M!*w:= (size_splits (e:=e) _).trans (add_le_add_right (hx.trans (mul_le_mul_of_nonneg_left (size_refund ..) (dwindles ..))) _)
    have hv:= hc.positive; have hu:0 ≤ w:= size_ge _
    have h' : A*M! ≤ 1/2:=le_trans (mul_le_mul_of_nonneg_right (show A≤10*A^3 from (show A≤A^3 by simpa only [pow_one] using (pow_le_pow_right₀ hv (by decide:1 ≤3))).trans (le_mul_of_one_le_left (by positivity) (by norm_num))) (dwindles C i)) ht
    have hew:w≤ A*(q+M!*w):=hp.trans (mul_le_mul_of_nonneg_left hf (zero_le_one.trans hv)); change w ≤ 2*A*q; linarith only [hew,mul_le_mul_of_nonneg_right h' hu]
lemma reduced_part (v:S) (ht:sufficient C i A) : ∃ x:S,ΠΩ x=0 ∧ (T) (U x)=(T) v:=by
    let P:=ΠΩ; let V':= P.ker; let b:= T; let g:= (b.comp U.toLinearMap).comp V'.subtype; let G₀:= g.codRestrict V' (fun v=>zero_high _)
    have hv: Surjective G₀:= LinearMap.injective_iff_surjective.mp (LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (fun i hi=> ?_)))
    · obtain ⟨x,hx⟩:=hv (⟨b v,zero_high v⟩:V'); exact ⟨x.val,x.property,congr_arg Subtype.val hx⟩
    apply Subtype.ext; change i.val=0;apply norm_le_zero_iff.mp
    have hi: b (U (i.val))=0:= congr_arg Subtype.val hi
    have hp:= hc.stays i.val (LinearMap.mem_ker.mp i.property) ht
    change _≤ 2*A*size (b (U i.val)) at hp; rw [hi,size_zero,mul_zero] at hp; exact (size_norm _).trans ((size_refund ..).trans hp)
-- cone control
abbrev grow (A:ℝ):ℝ := 4*A^2
lemma Costume.orth (he:e<d)(ht:sufficient C i A)(x:S)(hx: size x ≤ ((L).val:ℝ)* size (ΠΩ x)):
    size (U x) ≤ grow A * size (ΠΩ (U x)) ∧ ((L).val:ℝ)^(d-e)*size (ΠΩ x) ≤ 2*A*size (ΠΩ (U x)):=by
   let y:= Ω x; let Y:= U x; let m:= size (ΠΩ y); have hl:=hc.positive; have hh:0 ≤ m:=size_ge _
   have he': ((L).val:ℝ)^(d-e) * size (ΠΩ x) ≤ m:= first_low x
   have hw:size ((T) y) ≤ m:=by
       apply le_trans (overhead x he); apply le_trans _ he'
       apply le_trans (mul_le_mul_of_nonneg_left ((atop (e:=e) x).trans hx) (pow_nonneg (by positivity) _)) (le_of_eq ?_); rw [←mul_assoc,← pow_succ]; congr 2; omega
   have hY : size y≤ 2*m:= le_trans (size_splits y) (by linarith only [hw]); have hy:size Y ≤2*A*m:= (hc.body x).trans ((mul_le_mul_of_nonneg_left hY (zero_le_one.trans hl)).trans_eq (by ring));
   obtain ⟨z,hz,hL⟩:= reduced_part hc Y ht
   have hez: size (Ω z)≤ 4*A^2*m:= (hc.stays z hz ht).trans (le_trans (mul_le_mul_of_nonneg_left (hL.symm ▸ ((atop (e:=e) Y).trans hy)) (by positivity)) (le_of_eq (by ring))) -- rewrite direction
   let q:= x-z; have hQ : (T) (U q)=0:= by unfold q; rw [map_sub,map_sub,hL]; exact sub_self (_) -- fix
   have hv: size (U q)=size (ΠΩ (U q)):= congr_arg size (sub_eq_zero.mp (show U q-ΠΩ (U q)=0 from hQ))
   have hφ : m ≤ A* (size (ΠΩ Y)+size (ΠΩ (U z))):=by
       have hk: (ΠΩ) y= (ΠΩ) (Ω q):=by unfold q; rw [map_sub,map_sub,swell_mark z,hz,map_zero,sub_zero]
       have hf:= hc.hat q; unfold m; rw [hk]; rw [hv] at hf; refine (le_trans (size_cap ..) hf).trans (mul_le_mul_of_nonneg_left ?_ (zero_le_one.trans hl)); unfold q; rw [map_sub,map_sub,sub_eq_add_neg]; exact (size_add ..).trans_eq (by rw [size_neg])
   have hs:= (hc.sides z hz).trans (mul_le_mul_of_nonneg_left ((size_refund ..).trans hez) (dwindles C i))
   have hp : m ≤ 2*A*size (ΠΩ Y):=by
       have hM: M!*A^3*4 ≤ (1/2:ℝ):= le_trans (by have hM:=dwindles C i; nlinarith only [mul_nonneg hM (pow_nonneg (zero_le_one.trans hl) 3)]) ht -- defeq
       linarith only [hφ,mul_le_mul_of_nonneg_left hs (zero_le_one.trans hl),mul_le_mul_of_nonneg_right hM hh]
   refine ⟨hy.trans ((mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq (by unfold grow; ring)),he'.trans hp⟩
end YM.RG05Readout.Planes
