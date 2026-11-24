import YM.Contacts.Trails.Seat
/-! # One-step of actual history with estimated coupling and strengths. This is NOT at the old
 coarser beta. Need demonstrate evaluation from same starting history in invoking. -/
noncomputable section
set_option autoImplicit false
namespace YM.PhysicalNext.Repeat.Legato.Euro
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Concert ThroughLaunch Pressure Testing Contacts.Allium Contacts.Allium.Grant
open Contacts.Bounty.Trophy.Lore Contacts.Bounty.Trophy Contacts.Revest Contacts.Revest.Outlay
open Push.SectorMeasure Terrain ConnectedActivityE6 Blaze Contacts.Milling Sequin
open YM.Contacts.Barrage YM.Contacts.Allium.Grant.Warm YM.Contacts.Barrage.Reserve YM.Pulse Lumen Steam Resetter -- prefix issue
variable {m k n r N i j d:ℕ} {l t:ℝ}
section core
variable (u:Passage G)(hG:G.Simple)(X:G.ColorIndex) (p: Mirage u.M.K u.A.B.a u.M.O) (E:∀ m:ℕ,RackCore u.A.B.a u.A.B.M m)
set_option quotPrecheck false
local notation "A" => u.A.B.a
local notation "x₀" => u.A.B.a.clock.hatBeta m
local notation "J" => (u.A.B.a.clock.J (m+1))
local notation "I" => u.A.B.a.clock.J m
local notation "θ" => (u.A.B.a.clock.allowance)
local notation "U" => u.A.B.a.S
local notation "Q" => u.A.B.kin
local notation "μ" => u.X.shape.μ J I
local notation "P" => u.A.B.a.params m
local notation "F'" => u.A.B.a.params (m+1)
local notation "T" => coordinate u p hG
local notation "F" => (T).incident X E
local notation "κ" => (T).entry X E
local notation "S" => u.A.B.a.S.side m n
-- certificate interfaces.Trunk. aux Glow supplies production. Kernel exactly.
local notation "H"=> u.T.history N n
open Anthem
open Euro.Mint
namespace Trek
-- Competes includes all through top.Maker.Relays. estimates under woken part.
local notation "β"=> Mint.Charge (N:=N) u hG X p E
local notation "σ"=> (fun i=> Euro.grow u l i r)
variable (k l m n r N)
-- Pace c..V. syntax θ.
abbrev Spot (U₀:Rep G (u.A.B.a.S.side (m+1) n))(U₁:Rep G (u.A.B.a.S.side m n)) := let a':= Charge u hG X p E (N:=N) m k U₀.beta; ∃ Z:Helm u.X m n N k k (F (m+1) N) (F m N) U₀, U₁= Z.crown a'∧ Games u.X m n N k k (F (m+1) N) (F m N) U₀ l (σ (m+1)) a' Z
structure Tram (Z:Trail u.A.B.a n) : Prop where
   ordering : m≤ r ∧ r < N
   age i : r< i→ Z i=u.T.history N n i
   halo : Mint.RedLoan u hG X p E r n N (Z r) k
   Moor : Competes u.A.B.bake n N m Z
   move i : m ≤ i → i<N → u.A.B.Move N i n (Z i) (Z (i+1))
   graph i : m≤ i → i< r → Spot i k n r N l u hG X p E (Z (i+1)) (Z i) -- arg order printed
variable {k l m n r N} {Z: Trail u.A.B.a n} (W: Tram m k n r N l u hG X p E Z)
include W
lemma sail (hz:m≤ i)(hi:i< r):∃ B:Helm u.X i n N k k (F (i+1) N) (F i N) (Z (i+1)), Z i=B.crown (β i k (Z (i+1)).beta) ∧ Games u.X i n N k k (F (i+1) N) (F i N) (Z (i+1)) l (σ (i+1)) (β i k (Z (i+1)).beta) B:= W.graph i hz hi
lemma wealthy (hm':m≤ i)(hi:i ≤ r) : Truth (Z i) k (F i N) (σ i) (θ i):= by
   rcases lt_or_eq_of_le hi with hi|rfl
   swap; · dsimp only; rw [Euro.self]; exact W.halo.2.1
   obtain ⟨Z',h,h'⟩:= sail u hG X p E W hm' hi; dsimp only; rw [Euro.base u r l i hi,h]; exact h'.land
-- physical time differences from Canon, per step bounded uniformly 2 independent of shutters. preserve lanes. §wmcon needs local estimates on windows of finite relative lengths. No estimate on comparing reps per se; equality of density via Move.
lemma fisher (hv:m≤ i)(hx:i ≤ N): |(Z i).beta-(H i).beta| ≤ 2*((r-i:ℕ):ℝ):= by
   by_cases ht:i≤ r; swap; · rw [W.age i (by omega)]; simp
   induction ht using Nat.decreasingInduction with
   | self=> rw [show (Z r).beta= _ from W.halo.2.2.1]; simp
   | of_succ i hi ih=>
      have hn:i<N:= hi.trans W.ordering.2; let v j:= (Z j).beta; let w j:= (H j).beta; let b:=2*((r-i:ℕ):ℝ); let a:= (Q).alpha N i; have hp : |v i-v (i+1)-a|≤1:= (W.move i hv hn).δ; have hk: |w i-w (i+1)-a| ≤1:= (u.T.moves N i n hn).δ; have he:|v (i+1)-w (i+1)|≤ b-2:= by
          apply (ih (by omega) hn).trans_eq; unfold b; rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      exact abs_le.mpr ⟨by linarith [(abs_le.mp hp).1,(abs_le.mp hk).2,(abs_le.mp he).1], by linarith [(abs_le.mp hp).2,(abs_le.mp hk).1,(abs_le.mp he).2]⟩
omit W
variable (hk:2≤k)
include hk
lemma embarked (hl: Candles X u.X k r l)(hf: Wealthy (X:=X) hG p E k r N)(hr:r<N): ∃ Z: Trail A n, Tram r k n r N l u hG X p E Z:= by
   obtain ⟨V,hV⟩:= Mint.boot u hG X p E (n:=n) hl hf hk hr; let W :Trail (A) n:= H; let Z:= update W r V; have he i (hi:r< i): Z i=W i := update_of_ne hi.ne' ..; have hv:Z r=V:=update_self ..; have ht(i:ℕ)(hi:r≤ i)(hx:i<N): u.A.B.Move N i n (Z i) (Z (i+1)):= by
       rw [he (i+1) (by omega)]; rcases eq_or_lt_of_le hi with rfl|hl; rw [hv]; exact hV.1; rw [he i hl]; exact u.T.moves _ _ _ hx
   let h:= u.T.sticks N n; refine ⟨Z,⟨⟨le_rfl,hr⟩, he, hv.symm ▸ hV,⟨?_, (he _ hr).symm ▸ h.fromTop, fun i hi hk=> u.A.B.links hk (ht i hi hk)⟩,ht,fun i h h' => (Nat.not_lt_of_ge h h').elim⟩⟩
   intro i hi hm; have hv':= h.prices i (Nat.zero_le _) hm; rcases eq_or_lt_of_le hi with rfl|hi; rw [hv]; exact ⟨hV.1.bundle,hV.2.2.1 ▸ hv'.2⟩
   rw [he i hi]; exact hv'
lemma descend (hp:m<r)(hd:window u m r)(hl: Candles X u.X k m l)(hf: Wealthy (X:=X) hG p E k m N) (hw: Tram (m+1) k n r N l u hG X p E Z): ∃ Y, Tram m k n r N l u hG X p E Y:= by
   let z:= Z (m+1); have hr: m<N:= hp.trans hw.ordering.2; obtain ⟨ha,hb⟩:= hw.Moor.prices (m+1) le_rfl hr; have hc:= wealthy u hG X p E hw (i:=m+1) le_rfl hp; let t:= σ (m+1);
   obtain ⟨B,hXp⟩:= Mint.borning u hG X p E hl hf hk hr hb ha (rents u r l (m+1)|>.1) (rents u r l (m+1)|>.2) hc -- H notation issue
   let a:= β m k z.beta; let Y':= B.crown a; let V:= update Z m Y'; have hv : V m=Y':=update_self ..; have he (i:ℕ)(hi:m< i): V i=Z i:= update_of_ne (by omega) ..; have hL (i:ℕ)(hi:m≤ i)(hh:i<N): u.A.B.Move N i n (V i) (V (i+1)):= by
       rw [he (i+1) (by omega)]; rcases eq_or_lt_of_le hi with rfl|hi; rw [hv]; exact hXp.link; rw [he i hi]; exact hw.move i hi hh
   refine ⟨V,⟨hp.le,hw.ordering.2⟩,fun i hi=> by rw [he i (hp.trans hi)]; exact hw.age i hi, (he _ hp).symm ▸ hw.halo,⟨?_,(he _ hr).symm ▸ hw.Moor.fromTop,fun i hi hr=> u.A.B.links hr (hL i hi hr)⟩, hL,?_ ⟩
   · intro i hi hp; rcases eq_or_lt_of_le hi with rfl|hi; swap; · rw [he i hi]; exact hw.Moor.prices i hi hp
     have hh:= hL _ le_rfl hr; refine ⟨hh.bundle, passport (n:=n) u hG (t:=(V m).beta) hp hd ?_⟩; have ht:= fisher u hG X p E hw (i:=m+1) le_rfl hr; have hv':=(u.T.moves N m n hr).δ; have hC:=hh.δ; rw [he (m+1) (by omega)] at hC; let B:=(r-m:ℕ); rw [Nat.cast_sub (by omega), Nat.cast_add,Nat.cast_one] at ht; rw [Nat.cast_sub (by omega)]; obtain ⟨h₁,h₂⟩:= abs_le.mp hv'; obtain ⟨h₃,h₄⟩:=abs_le.mp hC; obtain ⟨hA,hB⟩:= abs_le.mp ht; exact abs_le.mpr ⟨by linarith only [hA,h₂,h₃],by linarith only [hB,h₁,h₄]⟩
   intro i hi hr; rw [he (i+1) (by omega)]; rcases eq_or_lt_of_le hi with rfl|hi; · rw [hv]; exact ⟨B,rfl,hXp⟩
   rw [he i hi]; exact hw.graph i hi hr
variable (hv: ∀ i,m ≤ i→ i≤r→ Candles X u.X k i l ∧ Wealthy (X:=X) hG p E k i N)
include hv
-- does not select outputs outside requested h. Can concatenate but guarantees nothing on lanes beyond.
lemma summon (hi:m≤ r)(hj:r<N)(hp:window u m r): ∃ Z,Tram m k n r N l u hG X p E Z:= by
   induction hi using Nat.decreasingInduction with
   | self=> exact embarked u hG X p E hk (hv r le_rfl le_rfl|>.1) (hv r le_rfl le_rfl|>.2) hj
   | of_succ m hi ih=>
      obtain ⟨Z,hZ⟩:= ih (fun i hx hr=> hv i (by omega) hr) (opens u hG (by omega) hp); exact descend u hG X p E hk hi hp (hv m le_rfl hi.le|>.1) (hv m le_rfl hi.le|>.2) hZ
end Trek
end core
end YM.PhysicalNext.Repeat.Legato.Euro
