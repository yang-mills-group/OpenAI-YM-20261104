import YM.MergeProof.North.Brim
import YM.Frontier6.Multi.Toll.Ledger

/-! Geometric preps and actual pairwise-gapped MULTI chain stamped.  Small
leaf extent sufficient, no assumptions at period fixed; eventual period tail.
Distinguish root anchor is (Cover 0), from output centroid on physical channel. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Filter Lattice RG Wilson MergeProof Ribbons Canopies Finset Accent Fareway Extra.Histories Bid
open Canopies.Doors -- resolve
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage Push Marker
open Next.Rank Next.Rank.Station Cells Extraction
open scoped Topology BigOperators Classical
variable {G:Gauge}{O:Type}[Fintype O][DecidableEq O]
variable (C:Family G) (p m j i k b d:ℕ)(t:O→ℕ)(x:O→ Cover)
set_option quotPrecheck false
local notation "Q"=> C.path.levels
local notation "P"=> C.path.levels.budget
local notation "δ"=> renal C.path.levels
local notation "η"=> near C.path.levels
local notation "X"=> bling C.path.levels

lemma loops_zero (a:Site (C.side j p)) (hi:i ≤ j)(hp: 2*‖C.S.place a‖≤ C.S.a i) : loops C j p a i=0:=by
    let v:=loops C j p a i; let Z:= C.S.toDepth hi p; let B:= separation v 0; let c:= Z.count.val
    have hV:2*separation a (Z.embed v) < c:=by unfold v; rw [vote C _ _ _ _ hi]; exact midway _ (C.S.toDepth_odd hi p) _
    have hz : separation (Z.embed v) 0 = c*B:=by nth_rw 1 [show (0:Site (C.side j p))=Z.embed 0 from Z.root.map_zero.symm]; exact Station.both ..
    have hq:= separation_triangle (Z.embed v) a 0; rw [separation_comm (Z.embed v) a,hz] at hq
    have hy : C.S.a j*c=C.S.a i:= C.S.embeds_scale Z; have ha:= C.S.a_pos j; have hf:2*separation a 0 ≤ c:=by
       rw [← hy] at hp; exact_mod_cast (le_of_mul_le_mul_left (a:=C.S.a j) (show C.S.a j*(2*(separation a 0:ℝ)) ≤ C.S.a j*c from (by linarith only [hp,(normC C j p a).1])) ha : (2:ℝ)*(separation a 0) ≤ c)
    by_contra h; have he : c≤c*B:= le_mul_of_one_le_right (Nat.zero_le _) (separation_pos _ _ h); omega

lemma grid_sub (x y:Cover) : C.S.gridPoint j (x-y)= C.S.gridPoint j x-C.S.gridPoint j y:=by ext i; simp [Schedule.gridPoint,mul_sub]
lemma weeds (hx:Pairwise (fun l h=> 2*C.S.a j*(C.path.levels.budget j).B^2 ≤ ‖C.S.gridPoint j (x l)-C.S.gridPoint j (x h)‖)) : ∀ᶠ p in atTop, Pairwise fun l h=> (C.path.levels.budget j).B^2 ≤ separation (wrap (C.side j p) (x l)) (wrap _ (x h)):=by
    filter_upwards [eventually_all.mpr (fun l:O=> eventually_all.mpr (fun h:O=>faraway C j (x l-x h)))] with p hp
    intro i k hi; have he:= ((normC C j p (wrap (C.side j p) (x i-x k))).2); rw [hp i k,grid_sub] at he
    rw [map_sub,separation_comm _ 0, show separation (0: Site (C.side j p)) (wrap (C.side j p) (x i)-wrap (C.side j p) (x k))= _ from ?_] at he -- test
    · exact_mod_cast (le_of_mul_le_mul_left (le_trans (hx hi) he) (mul_pos zero_lt_two (C.S.a_pos _)))
    rw [separation_comm]; unfold separation; simp

variable (v : (i:O)→ C.label (t i))(root:O)(H:Extraction.Order)
    {r:ℕ→ℕ}{D:∀ N p i,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable {W:Worth}{u₁ ψ:ℕ→ℝ}(hW:Scrim C W u₁ ψ (near C.path.levels) (renal C.path.levels) (fly C.path.levels) r D)(χ:ℕ→ℝ) (hV: WaresAll C (μ:=D) (r:=r) («δ»:=renal C.path.levels) (C.ref d) d χ (renal C.path.levels) (bling C.path.levels)) (hA:Created C)
    (hB:Stock.Tabs C.path.levels)(hc:C.Makes)
local notation "n"=> Fintype.card O

def leaves (N p:ℕ) := ∏ i:O, C.O N p (v i) (Cells.location C.S j N p (x i))
def leafGap (N p:ℕ)(z:C.label d):= leaves C j t x v N p-C.O N p z 0
structure Stamped (d:ℕ) (Q₀ y:ℝ) : Prop where
    probe : ∃ Z:Rowe C d,∀ᶠ i:ℕ×ℕ in H.fuse, ∃ hN:b ≤ i.1,
       let X0:=center C.S i.2 hN 0; let a:= leafGap C j d t x v i.1 i.2 (Z i)
       m≤ i.1∧ Next.UVStress.quota C d m i.1 i.2 (Z i) ≤ Q₀ ∧ Interior (X0.chamber 0) a∧ X0.rootTest (C.beta i.1 i.2) a ≤ y
include root hW hV hA hB hc
variable {ε A E B:ℝ}
lemma stamper (hh:m+1<j)(hb:b≤k)(hy:k ≤ m)(ht:Stock.Tabs.opens C.path.levels 1 b k)(hk:C.ref d ≤ k)(hj:∀ i:O,C.ref (t i) ≤ j)(hK:Fintype.card O ≤ r m)
   (hz:(C.S.a (m+1))*((C.path.levels.budget (m+1)).B^2+1:ℕ) ≤ C.S.a b)
   (hd:Pairwise (fun l h=>2*C.S.a j*(C.path.levels.budget j).B^2 ≤ ‖C.S.gridPoint j (x l)-C.S.gridPoint j (x h)‖))
   (he:∀ i:O,8*‖C.S.gridPoint j (x i)‖≤ C.S.a (m+1))(hT:GridApprox.room C.path.levels b m (lensScope C d))
   (hε:0<ε)(hε':ε ≤ 1)(hεX: ∀ i:ℕ,m < i→ i ≤ j→ ε ≤ restoreRate C.path.levels δ i) (B':O→ℝ)(hP:∀ i,0<B' i)(hT':∀ i,(C.labels.level (t i)).coeffSize (v i) ≤ B' i)(hQ:0<A)(hQ':A=charge C t B' j m ε)(hS:0 < B)(hS':E= needQuota C d m A)
   (hM: march (fun _:Unit=> B) η k m () ≤ δ m*(A/(16*X m))) (hF:32*(1+(Q|>.params m).columns)*B*‖alto C.path k d‖*(E/gainChart C.path m k) ≤ fly C.path.levels d k/2) : Stamped C m j b t x v H d (2*E) (2*(stakes C b k/B)):=by
    let w:=rootRate C t B' j
    let pred (i:ℕ×ℕ)(z:C.label d):Prop:=∃ hN:b≤ i.1,m ≤ i.1∧ Next.UVStress.quota C d m i.1 i.2 z ≤ 2*E ∧ Interior ((center C.S i.2 hN 0).chamber 0) (leafGap C j d t x v i.1 i.2 z)∧ (center C.S i.2 hN 0).rootTest (C.beta i.1 i.2) (leafGap C j d t x v i.1 i.2 z) ≤ 2*(stakes C b k/B)
    have hr : ∀ᶠ i:ℕ×ℕ in H.fuse,∃ z,pred i z:=by
       rw [Extraction.Order.fused,Extraction.Order.late];
       filter_upwards [H.per.cofinal.eventually (eventually_all.mpr (fun i:O=> faraway C j (x i))), H.per.cofinal.eventually (weeds C j x hd)] with p hp hL
       filter_upwards [H.mesh.cofinal.eventually (eventually_gt_atTop j), H.mesh.cofinal.eventually (near_center C b d hc), H.mesh.cofinal.eventually (eventually_all.mpr (fun i:O=>near_center C b (t i) hc))] with N hN hZ hB'
       let P' := H.per p; let N' := H.mesh N; change j < N' at hN; let hj' := hh.trans hN; let hm:= hb.trans hy; let hb':=hm.trans (m.le_succ.trans hj'.le); let T':=center C.S P' hb' 0
       let L i:= wrap (C.side j P') (x i); have hx(k:O): C.S.place (L k)=C.S.gridPoint j (x k):=hp k; have hs(k:O):loops C j P' (L k) (m+1)=0:= loops_zero C P' j (m+1) (L k) hh.le (by rw [hx]; linarith only [he k,norm_nonneg (C.S.gridPoint j (x k))])
       have hG : Travel C.path δ r D χ (0: Site (C.side b P')) (hands C P' b) (Equiv.swap 0) (Mix.camp C P' b) (placements C b j P' L) m j (C.ref d) ε N' := Canopies.Doors.route C b j P' L hW hV hm hh hN (hk.trans hy) hs (by
          exact_mod_cast (le_of_mul_le_mul_left (hz.trans_eq (C.S.embeds_scale (C.S.toDepth (hm.trans m.le_succ) P')).symm) (C.S.a_pos _))) hε hε' (fun _ hi hj=> hεX _ hi hj.le) hK
       let f i:= C.O N' P' (v i) (Cells.location C.S j N' P' (x i)); have hY(i:O):Interior (T'.chamber 0) (f i):=by
          apply hB' i hb'; rw [Cells.location,dif_pos hN.le,C.S.embeds_place]; exact ((hx i).symm ▸ (he i|>.trans (C.S.strictAnti.antitone (hm.trans m.le_succ))))
       have hU (z:C.label d):Interior (T'.chamber 0) (C.O N' P' z 0):= hZ hb' P' _ (by rw [latzero]; simp [(C.S.a_pos _).le]) z
       have hX (l:O):f l=C.O N' P' (v l) (placements C b j P' L N' (0,l)):=by unfold placements; rw [biteT C _ _ _ _ _ hb',vect C j P' N' (L l) hN.le]; unfold f Cells.location; rw [dif_pos hN.le]
       obtain ⟨z,hQz,hC'⟩:= Canopies.Doors.stamp C b j P' L hW hV w f (fun i=> C.continuousO ..) hc hA root hm hh hN hB ht hy hk t v (fun i=>plumR C (t i) (B' i) j) hG hs hL (fun i=>stockpit C _ _ _ (hP i)) hj (fun i=>paid_new C N' P' j (t i) hc _ _ (hP i) (hT' i) (hj i) hN) hX (fun _=> rfl) hY hU hT A E B hQ hS hQ'.le (ge_of_eq hS') hM hF -- needs room
       have hx:T' = center C.S P' hb' 0:= rfl
       exact ⟨z,hb',(m.le_succ.trans hj'.le), hQz, Next.UVStress.minus (show Interior (T'.chamber 0) (∏ i,f i) from (by rw [show (∏ i,f i)= fun x=>∏ i,f i x from (by ext; simp)]; exact Interior.combines f univ fun i _=>hY i)) (hU z),hC'⟩
    let Z(i:ℕ×ℕ): C.label d:= if h:∃ v,pred i v then h.choose else 0
    exact ⟨Z, hr.mono fun i h=>by change pred i (Z i); unfold Z; rw [dif_pos h]; exact h.choose_spec⟩
end YM.Frontier6.Road
