import YM.OPE.Compatible.Niche.Chute
import YM.OPE.Compatible.Brou.Pole
/-!
 # Tattoo.Era Bio.Pay. Arms & Foyers -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Owl
open Function Filter Set MeasureTheory Lattice Laurent RG Pressure Tree Precision Wilson Org RG.Supply Input
open PhysicalNext PhysicalNext.Repeat Legato Graces Roost PhysicalNext.Repeat.Aroma Pressure ConnectedActivityE6 Shell Channel Push.PriceCompiler Lass Zest
open Next.Free Woody Votive CardinalQ Stroke Stroke.MatchZ
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {ι :Type} {G :Gauge} {M: Metals G}
variable {P':Patch}{n N i j m l:ℕ}{C:ChartRatio G}{H:Sponsor G}{T:Seasons H}{p p':Clip}{X: Sheet G}
local notation "Z"=> X.profile
set_option quotPrecheck false
section Bank
open Push.PriceCompiler
abbrev ranksT (n:ℕ):= n+6+6
variable {f:LocalRatio C}{g:G.Simple}{L:PriceBook f T}{a:Axis}
structure Desk (X:Sheet G) (L:PriceBook f T)(a:Axis)(g:G.Simple) where
       stream :∀ l,Foyer L g a l (ranksT l)
       monotone (l j:ℕ) (hj:highStage L g a (stream l) ≤ j): ranksT l ≤ (X.profile j).order
       stretch (l:ℕ): l ≤ highStage L g a (stream l)
       OAuth (l j:ℕ)(hj:highStage L g a (stream l)≤ j): BankW L g a (stream l) hj (X.profile j).clip
variable (D:Desk X L a g)
noncomputable abbrev Desk.cost (l:ℕ):ℕ:= highStage L g a (D.stream l)
lemma Desk.sample (l:ℕ): 4 ≤ D.cost l:= (D.stream l).pay.st.S.order_cut
lemma Desk.from_a (T:Seasons H)(L:PriceBook f T) (X:Sheet G)(hx:Tendsto (fun i=> (X.profile i).order) atTop atTop) (a:Axis)(g:G.Simple): Nonempty (Desk X L a g):=by
       choose p hp hv using fun i:ℕ=> ((eventually_ge_atTop (max 5 (i+3))).and (hx.eventually_ge_atTop (ranksT i))).exists; choose S hS using fun i:ℕ=> Δtavern (l:=i) (d:=ranksT i) L g a (p i) (hp i) (Nat.le_add_right i 6 |>.trans (Nat.le_add_right _ 6)); refine ⟨S,?_,?_,fun l j v=>Classical.choice (stepW L g a _ v _)⟩
       · intro l j h; exact ((hv l).trans (show _≤_ from (X.orders (le_trans (hS l|>.symm|>.le) h)))) -- p extra
       intro l; exact (Nat.le_add_right l 3|>.trans ((le_max_right ..).trans (hp l))).trans (Eq.ge (hS _))
def Desk.relend (F:ℕ→ℕ): Desk (ThroughLaunch.raise X F) L a g:=by -- not lemma returns type fix
       exact ⟨D.stream,D.monotone,D.stretch,D.OAuth⟩
-- pace requests PRESERVEd after-L
private lemma τG (l:ℕ):0 < (D.stream l).pay.st.J:=by
      have he:=(D.stream l).pay.st.crisp; have hh:= (D.stream l).pay.st.S.coarse; rw [he] at hh; by_contra! hv; rw [Nat.le_zero.mp hv,pow_zero] at hh; exact (by decide : ¬3 ≤ (1:Side).val) hh
structure FrameBill (D:Desk X L a g)(S: Supply.Rolls X):Prop where
       marks (n l:ℕ)(hx:D.cost l≤ n): ∃ m:ℕ,S.L n=(D.stream l).pay.st.S.L^m
private lemma τL (n j:ℕ): ∃ Z0:Side,j ≤ Z0.val ∧ Large X n Z0 ∧ ∀ i:ℕ, i ≤ n → ∃ m:ℕ,Z0=(D.stream i).pay.st.S.L^m:=by
        let U:= Finset.range (n+1); let v:= ∏ i ∈ U,(D.stream i).pay.st.J; have hv:0<v:= Finset.prod_pos (fun i _=> τG D i); let p:Side:=(3:Side)^v; have hp:3 ≤ p.val:=by change 3 ≤ ((3:Side)^v).val; rw[PNat.pow_coe,show (3:Side).val=3 from rfl]; simpa only [pow_one] using (Nat.pow_le_pow_right (n:=3) (by decide) hv);
        have hH: Odd p.val:=by rw [show p=(3:Side)^v from rfl,PNat.pow_coe,show (3:Side).val=3 from rfl]; exact Odd.pow (by exact ⟨1,rfl⟩)
        let B:Patch:=⟨p,5,by omega,hp,hH⟩; obtain ⟨m,hT⟩:= Supply.Rolls.eventually_large X g n; obtain ⟨k,hk,hV,hN⟩:= widens B (max j m); refine ⟨p^k,le_trans (le_max_left ..) hk,hT _ ((le_max_right ..).trans hk) hV,fun i ht=>?_⟩ -- widens namespace
        obtain ⟨r,hr⟩:= Finset.dvd_prod_of_mem (fun i=>(D.stream i).pay.st.J) (Finset.mem_range.mpr (show i<n+1 by omega)); exact ⟨r*k,by unfold p; change v=_ at hr; rw [hr,(D.stream i).pay.st.crisp,pow_mul,pow_mul]⟩
-- simultaneous floors after actual core.C possible. stay monotone
lemma Desk.enrich : ∃ S:Supply.Rolls X,FrameBill D S:=by
       choose u hU ht hw using τL D; let A : ℕ→Side:=fun i=> Nat.rec (u 0 0) (fun j (v:Side)=>u (j+1) v.val) i; have hu :Monotone fun i=>(A i).val:= monotone_nat_of_le_succ (fun i=> hU ..); have he(k:ℕ):Large X k (A k):=by cases k <;>apply ht
       refine ⟨⟨A,he,hu⟩,⟨fun n i hi=>?_⟩⟩; have hz:=(D.stretch i).trans hi; cases n <;> apply hw _ _ i hz -- fix type local notation
end Bank
end YM.OPE.Owl
