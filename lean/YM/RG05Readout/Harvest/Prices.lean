import YM.RG05Readout.Pulse.Chills
/-!
# The receipt definition linking finite reg projection to full stack

Equality at all rooted branches with source test.Gather exact density from top marker polynomial.Actual motion of all mass preimages.Y.Authenticates
report coefficients. No frames here.Another extractor can reuse at b
asking same π.Uses the original affine convention of this calibrated C.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Harvest
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Shadow Flatten Nuclear Halls
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {j b k l:ℕ}{e:ℝ}(h:C.Makes)
set_option quotPrecheck false
local notation "t!"=> (1,false)
local notation "A!"=> C.path.levels
local notation "Λ"=> C.S.toDepth
local notation "L"=> C.path.levels.clock.op
local notation "R"=> C.path.rep N p
section
local notation "W!"=>Bin G (C.side n p)
local notation "Ω"=>Bin G (C.side (n+1) p)
local notation "O"=>Bin G (C.side N p)
abbrev BLight {X:Side} (F:Bin G X):= ∀ i,Integrable (F i) (prior G X)
lemma dye_grow {u:Goods G (C.side N p)} (h:C.Makes)(hu:Continuous u) : Integrable (fun U=> (( (C.path.rep N p N).eval U:ℝ):ℂ)*u U) (prior G _):= (((Complex.continuous_ofReal.comp (show Continuous (C.path.rep N p N|>.eval) from by rw [(h.wilson.starts ..).2]; exact bare_cont _)).mul hu).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
include h
lemma dye_bold (u:Goods G (C.side N p)) (hn:n ≤ N) (hu:Continuous u): Integrable (Records.dyes C n N p hn u) (prior G _) := gust_live _ _ _ _ _ (dye_grow h hu) _
lemma dye_plus (u v:Goods G (C.side N p)) (hn:n ≤ N) (hu:Continuous u)(hv:Continuous v): Records.dyes C n N p hn (u+v)=Records.dyes C n N p hn u + Records.dyes C n N p hn v:=by
    induction hn using Nat.decreasingInduction with
    | self=> simp_rw [Records.dyes, gust_base]; ext1 i; exact mul_add ..
    | of_succ i hi ih=> simp_rw [Records.dyes,gust_step _ _ _ _ _ hi]; unfold Records.dyes at ih; rw [ih]; exact StepData.push_add (C.path.levels.transition_mass ..) _ _ (dye_bold h u hi hu) (dye_bold h v hi hv) -- args h
omit h
lemma dye_pitch (u:Goods G (C.side N p)) (hn:n ≤ N)(t:ℂ): Records.dyes C n N p hn (t • u)= t • Records.dyes C n N p hn u:=by
    induction hn using Nat.decreasingInduction with
    | self=>simp_rw [Records.dyes,gust_base]; exact funext fun _=>mul_left_comm ..
    | of_succ i hi ih=> simp_rw [Records.dyes,gust_step _ _ _ _ _ hi]; unfold Records.dyes at ih; rw [ih,Address.preserves]
lemma dye_vac (hn:n ≤ N): Records.dyes C n N p hn 0=0:=by simpa only [smul_zero,zero_smul] using dye_pitch (C:=C) (p:=p) 0 hn 0
local notation "Y"=> journey C p n N d
abbrev sailS (C:Family G)(n p:ℕ) (F:Bin G (C.side (n+1) p)) (f:Body)(i:Address.Bud C p n):= F (Many.headFee C p n i f) ∘ Lattice.pull 1 (Address.child C p n i)
local notation "e₀"=> sailS C n p
lemma sail_lit (F:Ω)(hF:BLight F)(f:Body)(i:Address.Bud C p n): Integrable (e₀ F f i) (prior G _):=by
    let X:= F (Many.headFee C p n i f); change Integrable (stepUp t! (Address.child C p n i) X) _; exact tint (1,false) _ _ (hF _)
lemma sail_plus {F G':Ω}(hF:BLight F)(hG:BLight G') : Y (F+G')=Y F+Y G':=by
    funext f; unfold journey Address.average; change (Fintype.card _:ℂ)⁻¹ • (∑ i,blast C.path N p n d (e₀ (F+G') f i))=_; simp_rw [show ∀ i,e₀ (F+G') f i=e₀ F f i+e₀ G' f i from fun i=> rfl,blast,StepData.push_add (C.path.levels.transition_mass ..) _ _ (sail_lit F hF ..) (sail_lit G' hG ..), smul_add, Finset.sum_add_distrib]; rw [smul_add]; rfl
lemma sail_pitch (F:Ω)(t:ℂ) : Y (t • F)= t • Y F:=by
    funext f; unfold journey Address.average; change (Fintype.card _:ℂ)⁻¹ • (∑ i,blast C.path N p n d (e₀ (t • F) f i))=_; unfold blast; simp_rw [show ∀ i,e₀ (t • F) f i=t • e₀ F f i from fun i=> rfl,Address.preserves,smul_comm _ t,← Finset.smul_sum]; rw [smul_comm ..]; rfl -- dangerous simp looping
lemma sailed (F:Ω)(hF:BLight F):BLight (Y F):=fun f=>by unfold journey Address.average blast; apply Integrable.smul; exact integrable_finsetSum' _ (fun i _=> (StepData.push_integrable (C.path.levels.transition_mass ..) _ (sail_lit F hF f i)).smul _)
-- record stack.Item starting H:Dense.Directions with Origin.TTE.Bins.
variable (ht:n+1≤N)
noncomputable def arises (C:Family G)(p N n:ℕ)(hn:n+1≤N)(F:Bin G (C.side N p)) : Bin G (C.side (n+1) p) := fun f=> Records.dyes C (n+1) N p hn (F f)
noncomputable def pulls (C:Family G)(p N n d:ℕ)(hn:n+1≤ N)(F:Bin G (C.side N p))(m:ℕ)(he:m ≤ n): Bin G (C.side m p) := Nat.decreasingInduction (motive:=fun i _=> Bin G (C.side i p)) (fun i _=>journey C p i N d) (journey C p n N d (arises C p N n hn F)) he
variable (F:Bin G (C.side N p))(hm:m ≤ n)
local notation "v"=> pulls C p N n d ht -- edit
lemma wakes : v F n le_rfl= journey C p n N d (arises C p N n ht F):= Nat.decreasingInduction_self ..
lemma down (hv:m<n): v F m hv.le= journey C p m N d (v F (m+1) hv):= Nat.decreasingInduction_succ_left ..
variable (t:ℂ)
lemma budgets : v (t • F) m hm= t • v F m hm:=by
    induction hm using Nat.decreasingInduction with
    | self=> simp_rw [wakes]; rw [show arises C p N n ht (t • F) = t • arises C p N n ht F from funext fun u=>dye_pitch _ ht t,sail_pitch _ _]
    | of_succ i hi ih=> rw [down _ _ hi, down _ _ hi,ih,sail_pitch ..]
lemma vacC : v 0 m hm=0:=by simpa only [smul_zero,zero_smul] using budgets (d:=d) ht (C:=C) (p:=p) 0 hm 0
include h
abbrev timely {n:Side}(P:Bin G n):=∀ i, Continuous (P i)
lemma beacons (hf:timely F): BLight (v F m hm):=by
    induction hm using Nat.decreasingInduction with
    | self=>rw [wakes]; exact sailed _ (fun f=>dye_bold h (F f) _ (hf f))
    | of_succ i hi ih=> rw [down _ _ hi]; exact sailed _ ih
lemma doubles {F G':Bin G (C.side N p)}(hF: timely F)(hG: timely G') : v (F+G') m hm=v F m hm+v G' m hm:=by
   induction hm using Nat.decreasingInduction with
   | self=> simp_rw [wakes,show arises C p N n ht (F+ G')=arises C p N n ht F+ arises C p N n ht G' from funext fun f=> dye_plus h _ _ ht (hF f) (hG f)];exact sail_plus (fun f=>dye_bold h (F f) _ (hF f)) (fun f=>dye_bold h (G' f) _ (hG f))
   | of_succ i hi ih=> rw [down _ _ hi,down _ _ hi,down _ _ hi,ih]; exact sail_plus (beacons h ht F hi hF) (beacons h ht G' hi hG)
end
end YM.RG05Readout.Harvest
