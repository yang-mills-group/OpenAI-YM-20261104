import YM.OPE.Yarn.Tune
/-!
# Public radius tariff for Flex at an interval. Persistent paths budget differently.
`Short` circumstances are charged by fourth power ratio (sup time distance);
when the whole stride aligns, center horizon-zero avoiding this ratio tax. Keep
same theory & prescribed mill.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{n: Side} {C:Family G} {k z i j p N:ℕ}
variable {W r D}{σ χ:ℕ→ℝ} {K:ℕ}
set_option quotPrecheck false
local notation "P" => C.path
local notation "T" => C.path.levels
local notation "Γ" => C.path.levels.budget
local notation "Q" => C.path.levels.clock.hatBeta
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "ζ" => fly C.path.levels
local notation "R" => C.path.rep N p
variable (E:Tune C W r D σ χ) {X:Lamp G (C.S.side k p)} (o:∀ i:ℕ, Site (C.S.side i p)) (hp:∀ i, j ≤ i → i<k → (C.path.levels.clock.op i p).ratio.parent (o (i+1))=o i)
-- induction patterns
section aux
variable {H:History G}{a:ℝ}{w w':ℕ→ℝ} {ξ:∀ N p m:ℕ,m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}
    {o':∀ i:ℕ, Site (H.S.side i p)}{S:∀ i,Lamp G (H.S.side i p)} {X:Lamp G (H.S.side (k+1) p)} {e:k≤N}
lemma Drive_on (h:Drive H j k N p o' w ξ S e)(hv:∀ i,j < i→ i ≤ k→ w' i≤w i)(hf:∀ i,j < i→ i ≤ k→0<w' i): Drive H j k N p o' w' ξ S e:=by
   refine ⟨fun i hi he=>(h.drives i hi he).lower (hf _ (by omega) he) (hv _ (by omega) he)⟩
lemma Drive_first (he:k<N) (h:Debt H N p (ξ N p k he) (w (k+1)) (o' (k+1)) X (S k)) (hq:Drive H j k N p o' w ξ S he.le) : Drive H j (k+1) N p o' w ξ (Function.update S (k+1) X) he := by
   refine ⟨fun i hi hx=>?_⟩
   rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hx) with he'|rfl
   · rw [Function.update_of_ne (show i+1≠k+1 by omega), Function.update_of_ne hx.ne]; exact hq.drives i hi he'
   rw [Function.update_self, Function.update_of_ne hx.ne]; exact h
end aux
-- costs always for hi>lo.
def park (C:Family G)(u b:ℕ):= Loom.priced C u b (1/8) u
def soar (C:Family G)(b:ℕ):= (fly C.path.levels 0 b)/(256*(1+(C.path.levels.params (b-1)).columns)*C.path.levels.clock.hatBeta b)
def fee (C:Family G)(u b:ℕ) (long:Bool):= if long then soar C b else park C u b
variable {a : ℝ}
include E
lemma soar_pos (b : ℕ): 0 < soar C b:= by
   have h := (E.fog_mono 0 (Nat.le_refl b)).1; have hx := ((T).params (b-1)).columns_ge; have hz:1<Q b:=(T).fits.delayed _; unfold soar; positivity
lemma soar_le (v:ℕ): soar C v ≤ 1 := by
   let b:=1+((T).params (v-1)).columns; let c:= (Q) v; have hb:1 ≤ b:= le_add_of_nonneg_right (zero_le_one.trans ((T).params (v-1)).columns_ge); have hc:1 < c:=(T).fits.delayed _; let a:=256*b; have ha:1 ≤ a:=by unfold a; linarith only [hb]
   have hp:= (E.fog_mono 0 (Nat.le_refl v)).2.2; exact (div_le_one (zero_lt_one.trans_le (one_le_mul_of_one_le_of_one_le ha hc.le))).2 (hp.trans (one_le_mul_of_one_le_of_one_le ha hc.le))
include hp in
lemma short_pay (hj:j < k)(hl:C.ref 0 ≤ j)(hn:k ≤ N)(hx:0<a)(hv:X.Flex (C.path.rep N p k) (o k) (4*(1/a))) : ∃ S,S k=X ∧ Drive C.path j k N p o (fun _=>park C j k*a) D S hn:=by
    let w i:= priced C j k (a/8) i; have ha i: 0<w i:= price_pos (div_pos hx (by norm_num)); have he i (he:j ≤ i) (hp:i ≤ k): park C j k*a ≤ w i:=by
       have hh:w j≤w i:=by induction i,he using Nat.le_induction with
                             | base=>rfl
                             | succ i hi IH=> exact (IH (i.le_succ.trans hp)).trans (price_next hi (div_pos hx (by norm_num)))
       apply le_trans _ hh; unfold w park priced; apply le_of_eq; ring
    let v i:= 1/(2*w i)
    have hZ i (he:j ≤ i)(hξ:i ≤ k)(Y:Lamp G (C.side i p))(hF:Y.Flex (R i) (o i) (v i)): ∃ S,S i=Y ∧ Drive C.path j i N p o w D S (hξ.trans hn):= by
       induction i,he using Nat.le_induction with
       | base=> exact ⟨Function.update (fun _=> default) j Y, Function.update_self .., ⟨fun i hi he=>False.elim (Nat.not_lt_of_le hi he)⟩⟩
       | succ i hi IH=>
          have hP : i<N:= lt_of_lt_of_le hξ hn; have hK:= C.path.levels.transition_mass i p (R (i+1)).beta; have ht:= E.seed.wilson; have hO:= ht.represents N p (i+1) hP
          let L:= 6*((C.S.block i).val:ℝ); obtain ⟨f,K,hG,hg,⟨s,hs,hT⟩,he⟩:= slosh hF hO.good Y.lit ((E.sworn.brings i (hl.trans hi) N p hP).1) (by positivity) ((ht.represents N p i hP.le).good.labels) (ht.steps N p i hP|>.1.symm) hK; rw [hp i hi hξ] at hG
          let X' : Lamp G (C.S.side i p):=⟨f,K,hg⟩; have hw: X'.Flex (R i) (o i) (v i):= by
             apply hG.more; unfold v; rw [← mul_div_assoc]; have hh:= ha i; have hz:= ha (i+1); exact (div_le_div_iff₀ (by positivity) (by positivity)).2 (by linarith only [(show L*w i≤w (i+1) from price_march hi (div_pos hx (by norm_num)))] :6*_ * 1 * _ ≤ (_:ℝ)) -- annotation
          obtain ⟨X,hX,hV⟩:= IH (i.le_succ.trans hξ) X' hw; refine ⟨Function.update X (i+1) Y,Function.update_self ..,Drive_first hP ?_ hV⟩
          rw [hX]; refine ⟨⟨s,0,v (i+1),0,hs,hT,?_,by simp,by simp⟩, he.symm⟩; unfold v; rw [mul_div_cancel₀ _ (by have hh:= ha (i+1); positivity)]
    obtain ⟨S,hS,hZ⟩:= hZ k hj.le le_rfl X (by change Blade ..; apply (show Blade .. from hv).more; unfold v w; rw [price_top hj]; apply le_of_eq; ring_nf)
    refine ⟨S,hS,Drive_on hZ (fun i hi hk=> he i hi.le hk) (fun i hi hk=> mul_pos (price_pos (by norm_num)) hx)⟩
lemma long_pay (hj:j < k)(hl:C.ref 0 ≤ j)(hn:k ≤ N)(hx:0<a)(hv:X.Flex (C.path.rep N p k) (o k) (4*(1/a)))(hc:∀ i,j ≤ i→ i < k → o (i+1)= (C.path.levels.clock.op i p).ratio.embed (o i)):∃ S,S k=X ∧ Drive C.path j k N p o (fun _=>soar C k*a) D S hn:=by
    cases k with
    | zero=> omega
    | succ k=>
       let y:=1+((T).params k).columns; let t:=Q (k+1); let v:=4*(1/a); let w:=soar C (k+1)*a; have hj':j≤k:=Nat.le_of_lt_succ hj; have hy:1 ≤ y:= by have :=((T).params k).columns_ge; unfold y;linarith
       have ht:1<t:= (T).fits.delayed _; have hw:0 < w:= mul_pos (soar_pos E _) hx
       have he:=hc _ hj' (Nat.lt_succ_self k)
       have hX:256*y*t*soar C (k+1)=ζ 0 (k+1):=by unfold y soar t; rw [Nat.add_sub_cancel]; have he:=((T).params k).columns_ge; have h₀:= (T).fits.delayed (k+1); field_simp
       let x:= w*(t*v); have hΩ : w*32*y*(t*v) ≤ ζ 0 (k+1):= by
          calc _ = (256*y*t*soar C (k+1))/2 := by unfold w v; field_simp; ring
               _ ≤ _ := by rw [hX]; exact div_le_self (E.fog_mono 0 (Nat.le_refl _) |>.1.le) (by norm_num)
       have ht':0 < v:=mul_pos (by norm_num) (by positivity); have hw':w*(2*v) ≤ 1/2 ∧ w*(t*v) ≤ 1:=by
          have hz:= (E.fog_mono 0 (Nat.le_refl (k+1))).2.2; have hh:= hΩ.trans hz; have hi: w*(t*v)>0:=mul_pos hw (mul_pos (zero_lt_one.trans ht) ht'); have hh': w*(t*v) ≥ w*v:=mul_le_mul_of_nonneg_left (le_mul_of_one_le_left ht'.le ht.le) hw.le; constructor <;> nlinarith only [mul_le_mul_of_nonneg_right hy hi.le,hh',hh]
       obtain ⟨X',hD,P',hI⟩:= Patrol.ignite E.seed E.cuts.literal hn (by rw [← he]; exact hv) ((E.thor.moon N p k (hl.trans hj') hn).1.propagate) ((E.sworn.brings k (hl.trans hj') N p hn).2) (zero_le_one.trans ht.le) (by linarith only [hw'.1] : 2*w*(2*v) ≤1) (by rw [pow_zero,inv_one,norm_one,one_mul]; exact hw'.2); rw [pow_zero,one_mul] at hI
       obtain ⟨S,hk,hZ⟩:= Patrol.lantern (i:=j) _ _ E.seed E.cuts.system (k.le_succ.trans hn) hj' hl hI hw (fun i hi h' => (le_trans (le_of_eq (by unfold y v; ring): w* (32*(1+((T).params k).columns)*(t*v))≤ w*32*y*(t*v)) hΩ).trans (E.fog_mono 0 (h'.trans k.le_succ) |>.2.1)) (fun j ht hx=> hc j ht (hx.le.trans_lt k.lt_succ_self)) -- bracket
       exact ⟨Function.update S (k+1) X,Function.update_self ..,Drive_first hn (w:=fun _=>w) (by rw [hk,he]; exact hD) hZ⟩ -- rw dependent o k

local notation "L" => fee C
lemma voucher (hj:j<k)(K:Bool): 0<L j k K ∧ L j k K ≤1 :=by
   cases K
   case true=> exact ⟨soar_pos E k, soar_le E k⟩
   change 0 < park C j k ∧ park C j k ≤1; refine ⟨price_pos (by norm_num),?_⟩; unfold park priced; rw [if_pos rfl]; let c:= C.S.a k/C.S.a j; have hc: c ≤1:=(div_le_one (C.S.a_pos j)).2 (C.S.strictAnti.antitone hj.le); have hh: c> 0:= div_pos (C.S.a_pos _) (C.S.a_pos _)
   exact mul_le_one₀ ((mul_le_of_le_one_left (pow_nonneg hh.le _) (Real.rpow_le_one_of_one_le_of_nonpos ((T).fits.delayed (j+1)).le (by norm_num : -(2:ℝ) ≤ 0):δ j≤1)).trans (pow_le_one₀ hh.le hc)) (by norm_num) (by norm_num) -- edit η vs δ
include hp
lemma ripe (hj:j<k)(hl:C.ref 0 ≤ j)(hn:k ≤ N)(hx:0<a)(hv:X.Flex (C.path.rep N p k) (o k) (4*(1/a))) -- rename notation.LOOM price
    (long:Bool) (hx':long=true → ∀ i,j ≤ i→ i< k→ o (i+1)= (C.path.levels.clock.op i p).ratio.embed (o i)): ∃ S,S k=X ∧ Drive C.path j k N p o (fun _=>fee C j k long*a) D S hn:=by
    cases long; exact short_pay E o hp hj hl hn hx hv; exact long_pay E o hj hl hn hx hv (hx' rfl)
end YM.OPE.Yarn

