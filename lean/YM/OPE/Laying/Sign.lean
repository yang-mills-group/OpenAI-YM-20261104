import YM.OPE.Laying.Holding
/-! # Signed work steering exactly at a captured horizon -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Book
open Function Filter Finset Lattice RG Wilson Source Extra.Histories Labels Pressure
open Push Local Marker MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid Extra.Multi
open Cells MeasureTheory Motion Backup Float Drapery Playout.Rake
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{I J V:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]
    [Fintype V][DecidableEq V]{k i j b q p N d T :ℕ}{w x y α x':ℝ}{W r D}
    (L:LogPackage C W r D)(h:C.Makes)
set_option quotPrecheck false
local notation "Y"=> C.path.levels
local notation "μ'"=> (waybill C.path.levels)
local notation "δ₀"=> renal C.path.levels
local notation "η₀"=> near C.path.levels
local notation "ζ"=> fly C.path.levels
local notation "Ξ"=> C.path.rep N p
local notation "ν"=> (fun i=> ((C.path.levels.budget i).supportExponent-3:ℝ))
variable {Θ: Playout C.path p b N V}{A:Fibers I J} {s:Ward (Names V I)} {s':Ward (Names V J)}{W₀:ℕ→I→ℝ}{φ:I→ℕ}
    {u:∀ i:ℕ,I→ Site (C.side i p)} {F:I→ Config G (C.side N p)→ℂ}
    {P:∀ i:ℕ,I→ Cup (C.path.rep N p i)} {z:Finset J}
-- the singular road requires perfectly centered in this scope
noncomputable def road (C:Family G) (i d:ℕ) (x:ℝ)(j:ℕ) := x*(C.S.a j/C.S.a i)^d
local notation "Ω"=> (fun i=> C.S.a i)
local notation "r'"=> road C i d x
lemma born_road : road C i d x i=x:=by rw [road, div_self (C.S.a_pos i).ne',one_pow,mul_one]
lemma road_art (he:0<x) j : 0 < road C i d x j:= mul_pos he (pow_pos (div_pos (C.S.a_pos _) (C.S.a_pos _)) _)
lemma road_anti (he:0<x) : Antitone (road C i d x):= fun _ _ h=> mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_nonneg (C.S.a_pos _|>.le) (C.S.a_pos _|>.le)) (div_le_div_of_nonneg_right (C.S.strictAnti.antitone h) (C.S.a_pos _|>.le)) _) he.le
include L
local notation "Z"=> ζ d
lemma road_wealth (hG:G.Simple)(he:0<x)(hp:C.ref d ≤ k) : η₀ k*road C i d x k ≤ road C i d x (k+1):=by
    let H:ℝ:= (C.S.block k).val; let Y':= road C i d x (k+1); let T:= η₀ k; let q:= T*H^d; let r:= Z k; have hh:1 ≤ H:= one_le_two.trans (size_enough C.path k); have hT:0 < T:= L.system.costs.stay.water k (Nat.zero_le k)|>.1; have h':0 < r:= L.system.grows d k hp; have hH:0<H:=zero_lt_one.trans_le hh; have hq:0 ≤ q:=mul_nonneg hT.le (pow_nonneg hH.le _); have hu:= L.system.jump d k hp
    have ht:q*H*r ≤ r:=by rw [show q*H=T* H^(d+1) from by unfold q; ring]; exact hu.trans (flyAnti hG d k.le_succ)
    have hv:q ≤ 1:= (le_mul_of_one_le_right hq hh).trans (le_of_mul_le_mul_right (ht.trans_eq (one_mul _|>.symm)) h'); have hr:r' k=r' (k+1)*H^d:=by
       unfold road; rw [Schedule.a_step]; have hb:H≠0:=hH.ne'; -- remove. schedule.a_step n
       change x* (Ω k/Ω i)^d=x*(Ω k/H/Ω i)^d * H^d; have hu:Ω i≠0:= (C.S.a_pos _).ne'; simp only [div_pow]; field_simp
    rw [hr]; change T*(Y'*H^d) ≤ _; rw [mul_comm Y',← mul_assoc]; exact mul_le_of_le_one_left (road_art he (k+1)|>.le) hv
omit L
open Extra.Histories.Relay
lemma echo_road (k:ℕ) : road C i d x k*‖alto C.path k d‖=x* ‖alto C.path i d‖:=by
    rw [alto_norm,alto_norm]; unfold road; have hg:= C.S.a_pos k; have hh:=C.S.a_pos i; rw [div_pow]; change x*(C.S.a k^d/C.S.a i^d)*(C.S.a k^d)⁻¹=x*(C.S.a i^d)⁻¹; field_simp
local notation "F'"=> C.localSection d
local notation "E"=> standC C b N p
include L h
lemma Minted.sign {u:∀ i:ℕ,Site (C.side i p)} {p': Cup (C.path.rep N p i)} (hp:Minted C N p i d x' (u i) p') -- local x:P i

    {hx: i ≤ N} (hj:C.ref d ≤ k)(hm:k ≤ i)(hG:G.Simple)(he:0<x)(hw: x*‖alto C.path i d‖*stampOut C i d x'≤ζ d i){g:Extra.Histories.Music (C.labels.level d) C.path N p}(hE:Studio.Series C W (waybill (Y)) D N p d g)
    (hV:∀ m,k ≤ m→ m < i→ u (m+1)=(C.path.levels.clock.op m p).ratio.embed (u m)) : ∃ v:C.label d, (C.labels.level d).coeffSize ((g.tone i).index v) ≤ 2*stampOut C i d x' ∧∃ Y':∀ i:ℕ,Cup (C.path.rep N p i), Program C.path N p k i u Y' (road C i d x) D hx ∧ (∃ t H, Club C.path C.params F' (Z) μ' k i N p (road C i d x) D H t hx ∧ ∀ m:ℕ,k ≤ m→ m ≤ i→ Studio.Mantle C.path N p m F' (1,false) (u m) (H m) (Y' m))∧ ∀ Yh:Cup (C.path.rep N p i), Studio.Mantle C.path N p i F' (1,false) (u i) ((g.tone i).plays v) Yh→ Y' i=p'+Yh:=by
    obtain ⟨B,hB,hV',hA,hP⟩:=hp.bound; let r:=stampOut C i d x'
    obtain ⟨a,h_a,c,Y',Q,hQ,hX,hζ,hΩ⟩:=Program.erased F' (1,false) h.wilson (h.sections d) hE.echo hj hm hx (L.art hj) (w:=(road C i d x)) (fun _ _ _=> road_art he _) (fun i _ _=>road_anti he i.le_succ) hV hP hB hV' (show (C.labels.level d).coeffSize B.x+resQuote C i d x'≤2*resQuote C i d x' from (by linarith only [hA])) (show _ ≤ r from le_rfl) (fun m hk hv=>(by rw [echo_road]; exact hw.trans (flyAnti hG d hv)))
    refine ⟨a,h_a,Y',hQ,⟨c,Q,hX,hζ⟩,hΩ⟩

open Next.Rank
lemma holding (hm:Stock.Tabs.opens C.path.levels 1 b q)(hi:i≤N)(hk:q ≤ i) (hp:C.ref 0 ≤ b)(he:C.ref d ≤ q) {P :∀ i:ℕ,Cup (C.path.rep N p i)} (f:Config G (C.side N p)→ℂ) (hf:Continuous f)
    {H:∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p)} {t w:ℕ→ℝ}
    (hh: Club C.path C.params F' (ζ d) (waybill (Y)) q i N p w D H t hi) (hQ:Studio.Mantle C.path N p q F' (1,false) 0 (H q) (P q))(hx: (E).Market (Ward.all (Names (Site (C.side b p)) Unit)) (fun _:Unit=>0) (fun _=> P i) ((E).intention (fun _:Unit=> f) i hi) (fun _=>w i) (ν i))
    (hu:∀ m,q ≤ m→m ≤ i → 0<w m)(hT:∀ m,q ≤ m→ m < i → η₀ m*w m ≤ w (m+1))(hP: Program C.path N p q i (fun _=>0) P w D hi) : (center C.S p (hm.1.trans (hk.trans hi)) 0).rootTest (C.beta N p) f ≤ stakes C b q/w q:=by
    let z'(i):=(fun _ :Unit=> (0:Site (C.side i p))); have ht:= Work.I03.answer G C 1 le_rfl L.tabs b q hm N (hk.trans hi) p (hm.1.trans (hk.trans hi)); let Δ:= L.guide h hp; let V':=Site (C.side b p)
    let B(m):= ((E).spectrum m (z' m)); have he'(m)(v:V'×Unit): B m v= Mix.camp C p b m v.1:=by unfold B Playout.spectrum; simp [affine,z',standC]
    have hz(m:ℕ)(hv:q ≤ m)(hx:m ≤ i)(j): (E).occupied (r j) (z' m):=fun v=> (Occupancy.of_injective (show Injective (B m) from fun i j he=> Prod.ext (?_) (Subsingleton.elim ..)) v).trans (L.system.back _)
    swap
    · rw [he',he'] at he; rw [show Mix.camp C p b m= (C.S.toDepth (hm.1.trans hv) p).embed from funext fun i=> elev _ _ _ _ (hm.1.trans hv) _] at he; exact (C.S.toDepth (hm.1.trans hv) p).embed_injective he
    apply intakeLog L h f hf hm.1 hi hk he hh hQ; refine intervalMarket (W:=fun m (_:Unit)=> w m) (F:=fun i (_:Unit)=>P i) (P:=(E)) (t:=z') Δ (Trial.all Unit) hk hm.1 hm.1 hi (fun j hj hx _=>hu j hj hx) (fun j he hj a=>⟨ ?_, hT j he hj⟩) (fun j h hi=>⟨hz j h hi.le j,hz (j+1) (by omega) hi j,?_⟩) hx (fun _=>hf) (fun _=>hP) q le_rfl hk -- Ratio `parent zero`
    · let Y':= (Y).clock.op j p; change 0=(Y').ratio.parent 0; rw [← show (Y').ratio.embed 0=0 from (Y').ratio.root.map_zero]; exact (Ratio.embed_parent ..).symm
    intro v z ht' hZ; change _ ≤ separation (B j v) (B j z); rw [he',he']; have hZ': v.1 ≠ z.1:=fun h=>hZ (Prod.ext h (Subsingleton.elim ..)); have hw:= ht.2.2 j h (hi.le.trans ‹i ≤ N›) v.1 z.1 hZ'; rw [mul_one] at hw; exact le_trans ((Nat.mul_le_mul_left _ (meters L j).2.1).trans_eq ((pow_two _).symm)) (by exact_mod_cast hw)
end YM.OPE.Log.Book
