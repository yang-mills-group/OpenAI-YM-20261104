import YM.QuadraticLocal.Poetry.Beacons
import YM.QuadraticLocal.Poetry.Bear
/-!
# Abelian height subtraction near every primary anchor
Uniform torus bound in lifted coordinates independent of ALL images.MarkAlias.
 Only an iteration step in converting the leading not-yet-matched analytic vertex.
 No decomposition of heights assumed on true periodic flat.Link, only polynomial limits via Athena.KNOT.
 Adapt local transfer lemma on `size(lift wrap)` from `RG02.Pinned.Fields`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Poetry.Knot
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function AllOrder AllOrder.Fire AllOrder.Laplace AllOrder.Laplace.SigmaP AllOrder.Ker AllOrder.Ker.Start
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Field AllOrder.Ink.Money GaussianScore Module Push
open Sunrise Sunrise.Focus Haiku Stationary Pointwise Further.PhysicalPeriodLimitF933 Shingle Macrame
open Pinned Exterior
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{n m:Side}{a C D b:ℝ}{k:ℕ}
variable {V α M:Type}[Fintype α][Fintype M][DecidableEq M] (T:Finset M)(q:M)
local notation "J"=> Coarse G⊕M
local notation "Ω"=> Point (Coarse G⊕M)
local notation "U"=>rule (Coarse G⊕M) n
variable (F:AllOrder.Ink.Field (Coarse G⊕M)) (A: Stationary.Link G n)(v:rule M n) (x:Site n) (s:Cover→ G.Color)

-- aliases around E.At any lift height
set_option quotPrecheck false
local notation "U₀" => sendLink x A
local notation "τ"=> Echo.amplify n
local notation "W" i:max => Ink.Echo.arm n i
def configure (L:Macrame.Window n m k) : Site m:=0+wrap m (lift (x-L.cut 0))
lemma exactly (L:Macrame.Window n m k) : L.cut (configure x L)=x:=by unfold configure; rw [L.port,wrap_lift, add_comm,sub_add_cancel] -- okay.
local notation "z" i:max=> configure x (W i)
def poem (x:Site n)(q:Cover→G.Color) : BaseSites G n := fun i=> q (lift (i.1-x)) i.2.2
lemma grads (u:Cover)(i:Axis)(j:G.ColorIndex): gradientA G n (poem x s) (stood x (u,(Exterior.coord i,j))) = s (lift (wrap n (u+step i))) j - s (lift (wrap n u)) j:= by
 let y':= x+wrap n u; let i':= ((poem x s)); change arm G n 1 (gradientA G n i') (y',Exterior.coord i) j = _; rw [gradientC]; change s (lift (x+wrap n u+step i-x)) j - s (lift (x+wrap n u-x)) j=_; rw [add_assoc,add_sub_cancel_left, add_sub_cancel_left, ←wrap_step n,← map_add] -- subtraction simp?
lemma lift_light (q : Cover) (m : Side) : size (lift (wrap m q)) ≤ size q := by
   unfold size; refine Finset.sum_le_sum fun i _=>?_
   change (((↑(q i):ZMod m.val).valMinAbs).natAbs) ≤ (q i).natAbs
   by_cases h : (q i).natAbs ≤ m.val/2; swap
   · exact (ZMod.natAbs_valMinAbs_le _).trans (Nat.le_of_lt (not_le.mp h))
   obtain hu | hu := (q i).natAbs_eq
   · rw (occs:=.pos [1]) [hu]; rw [Int.cast_natCast, ZMod.valMinAbs_natCast_of_le_half h]; rfl
   rw (occs:=.pos [1]) [hu]; rw [Int.cast_neg,ZMod.natAbs_valMinAbs_neg, Int.cast_natCast, ZMod.valMinAbs_natCast_of_le_half h]; rfl
local notation "Y" k:max=> mingle ((convey (W k) A)-gradientA G (τ k) (poem (z k) s)) (convey (W k) v)
local notation "↑L"=> Letters
-- CARE † Coarse G = Orientation Body1 (TypeFace 1) × Color; axisEquiv.
abbrev paving (X: LinesC G)(ν:Point M→ℝ)(i:Point (Coarse G⊕ M)):ℝ:= i.2.elim (fun (k:Coarse G)=>X (i.1, Exterior.axisEquiv.symm k.1) k.2) (fun j=>ν (i.1,j))
abbrev cycles (i:Point (Coarse G⊕M)):= paving (sendLink x A-grad s) (v ∘ stood x) i
def page (k:ℕ)(i:Point (Coarse G⊕M)) := (Y k) (stood (z k) i) -- parse Y notation:k:max applies?
lemma noted (k:ℕ)(r : Cover)(i:Axis)(j:G.ColorIndex): page A v x s k (r,Sum.inl (Exterior.coord i,j))= A (x+wrap n r, Exterior.coord i,j) - (s (lift (wrap (τ k) (r+step i))) j - s (lift (wrap (τ k) r)) j):= by
 unfold page; let t:= (τ k); let L:= W k; let s':= z k; change convey L A (stood s' (r, Exterior.coord i,j)) - gradientA _ _ (poem s' s) (stood s' (r, Exterior.coord i,j)) =_; rw [Echo.rever,grads]; unfold L s'; rw [exactly]; rfl
lemma center (u:Cover): ∀ᶠ i:ℕ in atTop,lift (wrap (Echo.amplify n i) u)=u:= ((Echo.limitless n).eventually (eventually_gt_atTop (2*size u))).mono fun i h=> FreeResolvent.size_centers _ _ le_rfl h
lemma pointed (r:Cover)(i:M)(k:ℕ): page A v x s k (r,Sum.inr i)=v (stood x (r,i)):=by unfold page; change convey (W k) v (stood (z k) (r,i)) =_; rw [Echo.rever,exactly]
lemma trend (i:Point (Coarse G⊕M)): ∀ᶠ j:ℕ in atTop,page A v x s j i=cycles A v x s i := by
    rcases i with ⟨p,⟨l,j⟩|i⟩; swap; · exact Eventually.of_forall fun k=> pointed A v x s .. -- defeq?
    obtain ⟨i,rfl⟩:= Exterior.axisEquiv.surjective l; filter_upwards [center (n:=n) p,center (n:=n) (p+step i)] with k hk ht; unfold cycles; unfold paving; rw [show (Exterior.axisEquiv) i = Exterior.coord i from rfl]; rw [noted,ht,hk]; simp only [Sum.elim_inl]; rw [show Exterior.axisEquiv.symm (Exterior.coord i)=i from Exterior.axisEquiv.symm_apply_apply _]; rfl
local notation "ptS"=> pathGradient (sendLink x A)
local notation "C₀"=> ‖Exterior.arm G n 1 A‖ -- namespace station.Arm
open Picket
variable (hC:0≤C)(hs:∀ p:Cover,‖s p‖ ≤ C*size p)
include hs hC
lemma size_fee : ∃ c≥(1:ℝ), ∀ (i:Point (Coarse G⊕M)) j, ‖page A v x s j i‖ ≤ c*(1+size i.1):= by
 let c:=1+‖v‖+‖A‖+2*C; have h : 1≤c:=by unfold c; linarith [norm_nonneg v,norm_nonneg A]
 refine ⟨c,h,?_⟩; intro i j; rcases i with ⟨p,i|i⟩; swap; · rw [pointed]; exact (norm_le_pi_norm v _).trans ((by unfold c; linarith [norm_nonneg A] : ‖v‖ ≤ c).trans (le_mul_of_one_le_right (by linarith : 0≤c) (le_add_of_nonneg_right (by positivity))))
 obtain ⟨d,i⟩:=i; obtain ⟨d,rfl⟩:= Exterior.axisEquiv.surjective d; rw [show Exterior.axisEquiv d= Exterior.coord d from rfl,noted]; let u:=p+step d; have hδ(q:Cover): ‖(s (lift (wrap (τ j) q))) i‖ ≤ C*size q:= by apply le_trans ?_ ((hs _).trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (lift_light q (τ j))) hC)); exact (PiLp.norm_apply_le (p:=2) (s _) i)
 refine (norm_sub_le ..).trans ((add_le_add (norm_le_pi_norm A _) ((norm_sub_le ..).trans (add_le_add (hδ _) (hδ _)))).trans ?_); change ‖A‖+(C * size u+ _ )≤ _; have hv : (↑(size u):ℝ) ≤ size p+1:= by exact_mod_cast (show size u ≤ size p+1 from ((size_add ..).trans_eq (by rw [step_one d])))
 unfold c; dsimp only; nlinarith [mul_le_mul_of_nonneg_left hv hC, Nat.cast_nonneg (α:=ℝ) (size p),norm_nonneg A,norm_nonneg v]
end YM.QuadraticLocal.Poetry.Knot
