import YM.Contacts.Allium.BeaconHill
/-! # Reality.Drives Beacon at any rung. Supplies not estimates assumed on track. -/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts.Allium.Grant
open Function Filter Finset Lattice Gauge RG Matrix Wilson Milling Pulse Loom Flux Revest PhysicalNext.Repeat PhysicalNext.JointLoad.Heir Pressure Precision UVNext.CouplingReset
open Push.Uniform Pulse Spine Garf Steam House Exterior Model Arbor Province.Costing PertExtension.Series Radial
open Lintel Lintel.Angle Lintel.Plata Loom Junction Junction.Current Junction.Buyer Junction.Provision ConnectedActivityE6 Blaze Blaze.March Coat Meter Capture YM.Stationary Cove Lumen
open Resetter Sienna Next.Scheduling Barrage Barrage.Reserve Push.AbsoluteSums AnalyticBridge VerifiedReset Push.Uniform Roost Push.PriceCompiler
open Bounty.Trophy.Lore Bounty.Trophy Lattice RG Wilson RG.Supply Testing
open Tree Planned.JetPort Legato Spec Org
open scoped Topology ContDiff Classical NNReal BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {i i' i₀ j k m N n r d o:ℕ}{c c':Side} {X:G.ColorIndex} {l ξ: ℝ} {F: bore G} {t:Clip}
section mood
variable (X) (u:Passage G) (hg:G.Simple)(p : Mirage u.M.K u.A.B.a u.M.O) (E:∀ n,RackCore u.A.B.a u.A.B.M n)
local notation "e" => coordinate u p hg
local notation "W" => u.A.B.a.clock
local notation "Y" => u.A.B.a.S
local notation "Q" => u.A.B.kin
set_option quotPrecheck false
local notation "A" => (W).hatBeta m
local notation "J" => (W).J (m+1)
local notation "I" => (W).J m
local notation "B" => u.A.B.a.budget m
local notation "B'" => u.A.B.a.budget (m+1)
local notation "P" => u.A.B.a.params m
local notation "P'" => u.A.B.a.params (m+1)
local notation "F'" => (e).incident X E
local notation "R" => (e).entry X E m N
local notation "η" => (Q).path N m
set_option quotPrecheck false
local notation "S" => Odor.Winding.output e E X
open Item
variable (m N) (c)
def capture: Item G := ⟨A,c, R, F' m N,u.A.B.M.H N m, (Q).path N m,B, S m N c⟩
variable {m N c X u}
-- mint prices from Tall eventual m via CP5 and now. mask‐free.
include E X p hg
local notation "θ" => capture m N c X u hg p E -- arg order printed.
structure Wealthy (k m N :ℕ):Prop where
     pinCost i : i<k+3→ ‖pin (sink X ((e).entry X E m N)) i‖ ≤ lush ((e).a.clock.hatBeta m) ^ ((W).J (m+1))
     roots i r : i<k+3 → r<k+3 → r≠0→ ∀ c:Side, let y:= (e).Z m; let ℓ:= (e).haloSpan m; let F:=Odor.Winding.output (e) E X m N c; let s:= (W).J (m+1); Rooted (Range.cheap _) (hair ((e).incident X E m N) c i r) (y^s)∧ Rooted (Range.cheap _) (F i r) (y^s) ∧ Rooted (Range.cheap _) (hair ((e).entry X E m N) c i r-F i r) (hush ℓ c*y^s)
     box : Witnessed G k ((e).a.clock.hatBeta m) (u.A.B.a.params m) (u.A.B.a.budget m) ((e).incident X E m N) ((Q).path N m) (lush ((W).hatBeta m)^((W).J (m+1)+1)) (ConnectedActivityE6.loopBill G 1 ((W).hatBeta m))
     woods : Witnessed G k ((e).a.clock.hatBeta (m+1)) (u.A.B.a.params (m+1)) (u.A.B.a.budget (m+1)) ((e).incident X E (m+1) N) ((Q).path N (m+1)) (lush ((W).hatBeta (m+1))^((W).J (m+1)+1)) (ConnectedActivityE6.loopBill G 1 ((W).hatBeta (m+1))) -- allowance fine top extra one
omit E X p hg in
lemma Wealthy.hospital {Θ:BudgetPoint}{f:bore G}{T:PathData G}{P₀:Stage} -- notation risk
      {x Λ i v:ℝ}(h: Witnessed G k x P₀ Θ f T i Λ)(hr:i≤v): Witnessed G k x P₀ Θ f T v Λ:={h with fare:=⟨fun j r hu ht=> (h.fare.cap _ _ hu ht).weaken (fun _=> le_rfl) hr, h.fare.nonneg.trans hr⟩}
set_option maxHeartbeats 500000 in
lemma riches : ∀ᶠ m in atTop, ∀ N,m<N→ Wealthy (X:=X) hg p E k m N:= by
   let Q':= e; let n(i:ℕ):= (W).J (i+1); have hX(i:ℕ):= (e).flares X E i; have ht i:= (e).Z i; -- term ℝ
   obtain ⟨f,g,hf,hg',H⟩:= Odor.Winding.stroll (e) E X;
   have bloom (F:ℕ→ℝ)(hw:Q'.Fair F) : ∀ᶠ m:ℕ in atTop,F m≤(Q'.Z m)^((W).J (m+1)):= by obtain ⟨a,ha⟩:=hw.filled; filter_upwards [ha,u.A.B.a.fits.deep.eventually_ge_atTop a] with m ha he using ha.trans (pow_le_pow_right₀ (Q'.z_ge m) (he.trans (u.A.B.a.fits.mono (Nat.le_succ m))))
   have hv i r: ∀ᶠ m:ℕ in atTop,∀ N,m<N→ let c:= (e).Z m^((W).J (m+1)); ‖pin (sink X ((e).entry X E m N)) i‖ ≤ c ∧ ∀ p':Side,r≠0→ let q:= S m N p'; Rooted (Range.cheap _) (hair ((e).incident X E m N) p' i r) c ∧ Rooted (Range.cheap _) (q i r) c ∧ Rooted (Range.cheap _) (hair ((e).entry X E m N) p' i r-q i r) (hush ((e).haloSpan m) p'*c):= by
      let H' := ((e).rentLaw X E 3 le_rfl); obtain ⟨s,hs,hp⟩:= ((H' i r).law.1); obtain ⟨f₀,h₀,hf₀⟩:= Oasis.mintPin X (H' i 2).raw.1 le_rfl
      filter_upwards [bloom _ hs,bloom _ h₀,bloom _ (hf i r),bloom _ (hg' i r)] with v hx ht hb hr m hm C
      have hM:= hf₀ v m hm
      constructor;
      · by_cases h:i=0; · subst i; rw [show pin (sink X _) 0=1 from sink_mast _, norm_one]; exact one_le_pow₀ ((e).z_ge _)
        unfold pin sink; rw [PowerSeries.coeff_mk,if_neg h]; exact hM.trans ht
      intro V hk q; obtain ⟨he,h⟩:= H _ _ hm i r hk V; refine ⟨?_,he.weaken (fun _=> le_rfl) hb, ?_⟩
      · have hp:= (hp v m hm.le).weaken bath_terrace hx; letI:NeZero r:= ⟨hk⟩; refine (printFeeds (n:=V) (heritage (fun i'=>(e).wild X E v m hm.le|>.blazing.frame.here i' i r) _)).cost hp (fun _=>?_ ) (lower_onto _); exact le_trans (Range.wide (Range.cheap _) _ le_rfl (fun _ _=> le_rfl)) (Range.one_bill ..)
      rw [← neg_sub]; exact h.neg.weaken (fun _=>le_rfl) (mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr (Real.exp_pos _).le))
   let Z:= Finset.range (k+3); have he:= (eventually_all_finset Z).mpr fun i hi=> (eventually_all_finset Z).mpr fun r hr=> hv i r; have hf:= Model.Province.camp hg u X E p k -- typecheck
   filter_upwards [he, hf,(tendsto_atTop_mono (f:=id) (g:=fun x:ℕ=>x+1) Nat.le_succ tendsto_id).eventually hf] with m he hf hh n hm;
   exact ⟨fun i hi=> (he i (mem_range.mpr hi) 0 (mem_range.mpr (by omega)) n hm).1,fun i r hi hr hk p=> (he i (mem_range.mpr hi) r (mem_range.mpr hr) n hm).2 p hk, Wealthy.hospital (hf n hm.le) (pow_le_pow_right₀ ((e).z_ge _) (Nat.le_succ _)), Wealthy.hospital (hh n hm) (pow_le_pow_right₀ ((e).z_ge _) (u.A.B.a.fits.stepSlow (m+1)))⟩ -- definitional `tendsto id.addconst` wrong
end mood
end YM.Contacts.Allium.Grant
