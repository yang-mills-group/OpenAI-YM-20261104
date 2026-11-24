import YM.OPE.Samples.Band
import YM.OPE.Trunk.Tour
/-!
# Cost layout from actual gridded positions

Translate declared center to the origin. Pins every stage through which it
owns a class. Compare at that same origin; no assumption of alignment to any
leaf. Upper heights are the first for unit pricing (`j+1` with stationary pixel at both).
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk
open Rhythm Function Filter Finset MeasureTheory Lattice RG Wilson Source Extra.Histories Labels Pressure
open Push Local Marker MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open Cells Motion Extra.Multi Next.Rank Station
open Book Book.Mask PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}{C:Family G}{I J Z:Type}[Fintype I][DecidableEq I]
    {H i m j n p b q t N:ℕ}{Q: Rhythm I} {S:Loom Q} {x:I→ Cover}
set_option quotPrecheck false
local notation "Y"=> C.path.levels
local notation "T"=> C.S.gridPoint
local notation "Ω"=> C.S.a
local notation "K"=> (Y).budget
local notation "L!"=> S.launch Q.limit
variable (S)
-- point profile must align to previous launch, even for asleep arcs at that layer. actual sleepers' paths do follow because schedule constructed from positions
-- abbreviations
lemma zoom_inj (L: Schedule)(i:ℕ): Injective (L.gridPoint i):=by intro x y h; ext a; have ht:L.a i*x a = L.a i*y a:= congr_arg (fun x:E4=>x a) h; exact_mod_cast mul_left_cancel₀ (L.a_pos _).ne' ht
def Travel (S:Schedule)(j:ℕ)(x:E4): Prop:= ∃ y,S.gridPoint j y=x
variable {ξ z:E4}
lemma Travel.inh (h:Travel C.S i ξ)(ht:i ≤ j): Travel C.S j ξ:=by obtain ⟨u,rfl⟩:=h; exact ⟨_,zoom_grid ht u⟩
lemma Travel.add (h:Travel C.S i ξ)(he:Travel C.S i z):Travel C.S i (ξ+z):=by obtain ⟨_,rfl⟩:=h; obtain ⟨_,rfl⟩:=he; exact ⟨_,Work.B16.grid_add ..⟩
lemma Travel.null : Travel C.S i 0 := ⟨0,grid_zero ..⟩
local notation "u!"=> T (S.launch Q.limit) ∘ x -- binder implicit info fields set.S
local notation "E"=> standC C b N p
-- numeric guard equal consumption. Separation uses both rules when actors.
def priorL (t:ℕ): ℕ:= if t=0 then S.below 0 else S.launch (t-1)
lemma prior_le (he:t ≤ Q.limit) : priorL S t ≤ S.below t:=by
    cases t with
    | zero=> simp [priorL]
    | succ t=> simp only [priorL,add_tsub_cancel_right]; rw [if_neg (Nat.succ_ne_zero t)]; exact (S.upper _ he).le
structure Canvas (S: Q.Loom)(C:Family G)(H b:ℕ)(x:I→ Cover) : Prop where
    born : b ≤ S.below 0
    horizon : ∀ p,let h:=born; (C.path.levels.budget (S.below 0)).B^2+1 ≤ (C.S.toDepth h p).count.val
    align t : t ≤ Q.limit→∀ i,Travel C.S (priorL S t) (Q.point H (C.S.gridPoint (S.launch Q.limit) ∘ x) i t)
    closely t : t ≤ Q.limit→∀ i,4*‖C.S.gridPoint (S.launch Q.limit) (x i) - Q.point H (C.S.gridPoint (S.launch Q.limit) ∘ x) i t‖ < C.S.a (S.below t+1)
    begin_age i : Travel C.S (S.launch (Q.age i)) (C.S.gridPoint (S.launch Q.limit) (x i))
    spread i j : i≠j→let m:= S.launch (Q.gap i j); 2*C.S.a m*(((C.path.levels.budget m).B^2+2:ℕ):ℝ) < ‖C.S.gridPoint (S.launch Q.limit) (x i) - C.S.gridPoint (S.launch Q.limit) (x j)‖
namespace Canvas
-- geometry helpers
variable {S} (U:Canvas S C H b x){y y':Cover}
lemma neighbor (u : Cover)(hi:j ≤ n){p:ℕ} : (C.S.toDepth hi p).embed (wrap (C.side j p) u)= wrap (C.side n p) (zoom C.S hi u):=by
    rw [Ratio.embed_wrap,zoom]; rfl -- toDepth p counted same
lemma proximity (h: n ≤ m)(x y:Cover) (ht:2*‖T m x - T n y‖ < Ω n): ∀ᶠ p in atTop,(C.S.toDepth h p).parent (wrap (C.side m p) x)=wrap (C.side n p) y:=by
    let w:= zoom C.S h y; filter_upwards [faraway C m (x-w)] with p hp; apply Station.owner; apply (Nat.cast_lt (α:=ℝ)).mp; let X:=wrap (C.side m p); rw [neighbor y h]
    let Z:= C.S.toDepth h p; let i:= separation (X (x-w)) 0; let j:= separation (X x) (X w); have he:i=j:=by unfold i j separation; rw [sub_zero,map_sub]
    have hy:=normC C m p (X (x-w))|>.1; change (Ω m)*i ≤ ‖_‖ at hy; change C.S.place (X (x-w))= _ at hp
    rw [hp] at hy; rw [show T m (x-w)= T m x - T n y from (by apply eq_sub_of_add_eq; rw [← zoom_grid h y, show zoom C.S h y=w from rfl,← Work.B16.grid_add]; simp),he] at hy
    push_cast; change 2*(↑j:ℝ) < ↑Z.count.val; apply lt_of_mul_lt_mul_left _ (C.S.a_pos m).le; rw [C.S.embeds_scale Z]; linarith
lemma upshort (h:Travel C.S i (T j y))(hu:i ≤ j) (he:i ≤ m)(ht:m ≤ n) : loops C j p (wrap (C.side j p) y) n=(C.S.toDepth ht p).embed (loops C j p (wrap (C.side j p) y) m):=by
    obtain ⟨v,hv⟩:=h; have hh : zoom C.S hu v = y:= zoom_inj _ _ ((zoom_grid hu v).trans hv); subst y; rw [← neighbor]
    let Z:= wrap (C.side i p) v; let x:= (C.S.toDepth hu p).embed Z
    have he(l)(hl:i ≤ l) : loops C j p x l = (C.S.toDepth hl p).embed Z:=by
       rcases le_total j l with he|he
       · rw [vect C j p l x he]; exact (embed_comp (C.S.toDepth hu p) (C.S.toDepth he p) (C.S.toDepth hl p) Z).symm
       rw [vote C j p l x he]; unfold x; rw [embed_comp (C.S.toDepth hl p) (C.S.toDepth he p) (C.S.toDepth hu p), Ratio.embed_parent]
    -- he shadow?
    rw [he m ‹i ≤ m›,he n (le_trans ‹i ≤ m› ht)]; exact embed_comp (C.S.toDepth ‹i ≤ m› p) (C.S.toDepth ht p) _ Z
lemma again (k:Site (C.side j p))(h:m ≤ n) : (C.S.toDepth h p).parent (loops C j p k n)= loops C j p k m:=by
    by_cases hi:n ≤ j
    · rw [vote C j p n _ hi,vote C j p m _ (h.trans hi)]; exact (parent_nested _ (C.S.toDepth hi p) _ (C.S.toDepth_odd h p) (C.S.toDepth_odd hi p) _).symm
    have hk: j ≤ n:= le_of_not_ge hi; rw [vect C j p n _ hk]; by_cases he:j ≤ m
    · rw [vect C j p m _ he]; rw [embed_comp (C.S.toDepth he p) (C.S.toDepth h p) _,Ratio.embed_parent]
    have ht: m ≤ j:= le_of_not_ge he; rw [vote C j p m _ ht]; rw [parent_nested (C.S.toDepth ht p) (C.S.toDepth hk p) (C.S.toDepth h p) (C.S.toDepth_odd ht p) (C.S.toDepth_odd hk p),Ratio.embed_parent]
lemma custody {i j n:ℕ}(h:n ≤ i) (he:i ≤ j)(P:i ≤ m)(hp: m ≤ j){x:Site (C.side j p)}{w:Site (C.side n p)}(hh: (C.S.toDepth hp p).parent x = (C.S.toDepth (h.trans P) p).embed w): loops C j p x i=(C.S.toDepth h p).embed w:=by
    have ht:=again (C:=C) x P; rw [vote C j p m _ hp,hh,embed_comp (C.S.toDepth h p) (C.S.toDepth P p) _ w, Ratio.embed_parent] at ht; exact ht.symm
lemma expands (x:Site (C.side m p))(y:Site (C.side m p))(h : i ≤ m) : let Z:= C.S.toDepth h p; let v:=Z.count.val; let u:=v*separation (Z.parent x) (Z.parent y); u < separation x y + v∧ separation x y < u+v:=by
    intro Z v u; let t:=fun x: Site (C.side m p)=> separation x; let a:= Z.embed (Z.parent x); let b:= Z.embed (Z.parent y); have hU:u=t a b:=(Station.both ..).symm; have hx:2*t x a < v:= midway _ (C.S.toDepth_odd h p) x; have hy: 2*t y b < v:= midway _ (C.S.toDepth_odd h p) y
    have h' : t a b ≤ t x a+t x y+t y b:=(separation_triangle a x b).trans (by change t a x + t x b ≤ _; have hp:t x b ≤ t x y+t y b:= separation_triangle x y b; have ht:t a x=t x a:= separation_comm ..; omega); have h'' : t x y ≤ t a x+t a b+t b y:=(separation_triangle x a y).trans (by change t x a+t a y ≤ _; have hp:t a y ≤ t a b+t b y:= separation_triangle ..; have ht:t x a=t a x:=separation_comm ..; omega); change u < t x y+v ∧ t x y<u+v; have ht: t y b=t b y:= separation_comm ..; have ht':t x a=t a x:= separation_comm ..; omega
lemma bubbles (y y':Cover) (h:i ≤ j)(v:ℕ) (he:2*Ω i*(↑(v+1:ℕ):ℝ)< ‖T j y - T j y'‖) :∀ᶠ p in atTop,v ≤ separation (loops C j p (wrap (C.side j p) y) i) (loops C j p (wrap (C.side j p) y') i) := by
    filter_upwards [Cards.native_space (k:=j) C y y'] with p hp; let x:= wrap (C.side j p) y; let x':=wrap (C.side j p) y'; let Z:= C.S.toDepth h p; let a:= Z.count.val; let z:=separation (Z.parent x) (Z.parent x'); let d:= separation x x'
    have ht:a*(v+1)< d:=by
        apply (Nat.cast_lt (α:=ℝ)).1; apply lt_of_mul_lt_mul_left _ (show (0:ℝ) ≤ 2*Ω j from (mul_pos two_pos (C.S.a_pos _)).le); rw [← C.S.embeds_scale Z] at he; have hu:‖T j y-T j y'‖ ≤ 2*(Ω j*d):=hp; rw [Nat.cast_mul]; unfold a; linarith only [hu,he]
    rw [vote C j p i _ h,vote C j p i _ h]; have hp:d < a*z+a:= (expands x x' h).2; rw [mul_add,mul_one] at ht; exact Nat.le_of_mul_le_mul_left (le_of_lt (Nat.lt_of_add_lt_add_right (ht.trans hp))) Z.count.property
variable {W r D} (L: LogPackage C W r D)
include L
lemma common_dist (z z':Site (C.side m p))(h:i ≤ m)(he:(K i).B^2+1≤ separation ((C.S.toDepth h p).parent z) ((C.S.toDepth h p).parent z')) : (K m).B^2≤ separation z z':=by
    let Z:=C.S.toDepth h p; let t:= Z.count.val
    have hV:= Nat.mul_le_mul_left t he; rw [mul_add,mul_one] at hV; let P:=L.system.costs.stay; have hp:(K m).B^2 ≤ t * (K i).B^2:= gap_comp C p i m ⟨fun i _=> P.water i (Nat.zero_le _),fun i _=> P.mint i (Nat.zero_le _), fun i _=> P.split i (Nat.zero_le _),fun i _=> P.support i (Nat.zero_le _)⟩ h; exact hp.trans ((Nat.le_of_lt (Nat.lt_of_add_lt_add_right (hV.trans_lt (expands z z' h).1)))) -- implicit δ
end Canvas
end YM.OPE.Log.Trunk
