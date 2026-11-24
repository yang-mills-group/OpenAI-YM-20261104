import YM.MS.ScaleForest.SecondaryOsc
import YM.MS.ScaleForest.PackedPairs
/-!
# Fourier gain for between-pin joins, all continuation sectors

At the join edge the phase with two distinct anchors is rapidly effective.
This holds with all external momentum derivatives (the fields in the
uncontracted complement) under the `Outpost` condition:
uniform control of position frequency losses from above along with
Fourier gains from lower bounds. Keep primary
components as they are; estimate the remaining axis before doing the
charges with z. Applies with projected continuity estimates `fell`, no
automatic use of the integer-section pole calculation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect Tone Momentum Osc Fiddle
open scoped Topology ContDiff
variable {G : Gauge} {I E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
   [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
   {u v ξ c a b y : I→ℝ} {m n : ℕ} {s : ℂ} {K : Rip G} {X Y : I→ Mob G} {S : I→ℂ}
   {P : I→QP}

-- price before q integration
variable (hk : rPrice K) (hx : fell ξ a X) (hy : fell ξ b Y)
include hx hy hk

def brushWing (L:F→L[ℝ] SectorP m)(K : Rip G) (X Y : Mob G) (l r : Touch G m E) (i j : Cfield G m) := fun p:F×E => oneCross K X Y (L p.1) i j (sail l p.2) (sail r p.2)

theorem cost_before (L:F→L[ℝ] SectorP m) (K':SectorP m→L[ℝ] F)(hr:∀ q, K' (L q)=q)
    (l r : Touch G m E) (i j : Cfield G m) : quiet ξ (fun k=> brushWing L K (X k) (Y k) l r i j) (a*b) := by
   let T := F×E
   let B : F×E→L[ℝ] SectorP m:= L ∘L ContinuousLinearMap.fst ℝ F E
   let Z (l:Touch G m E) := Wire.lift l (ContinuousLinearMap.snd ℝ F E)
   have hp := (ride_peak ((Rock.transport (z:=ξ) hk) m i j) hr).rapid (F:=E)
   have he:= (hp.mul ((hx m (F×E) ((i,B)::Z l)).L (ContinuousLinearMap.mul ℝ ℂ (cross (parity j) (degree (field parity) l))))).mul (hy m (F×E) ((j,-B)::Z r));
   convert! he using 1; funext k p; simp_rw [brushWing, oneCross,sail_degree, fieldVal,sail_cons,Z,lift_sail]; rfl; funext i; simp

abbrev directs (m:ℕ)(p:Bool) : SectorP m×ℝ→L[ℝ] SectorP (m+1) := if p then slideA (Nat.lt_succ_self m) else -(slideA (Nat.lt_succ_self m))
def forge (A:QP)(q:SectorP m)(p : Bool) := waveFact (if p then A else -A) q

theorem directCost (p:Bool)(l r : Touch G m E)(i j:Cfield G (m+1)) : quiet ξ
    (fun k=> brushWing (directs m p) K (X k) (Y k) (Rock.move (Nat.le_succ m) l) (Rock.move (Nat.le_succ m) r) i j) (a*b) := by
   unfold directs; split_ifs with h
   · exact cost_before hk hx hy _ (backA (Nat.lt_succ_self m)) (fun p=> equal0 p _) _ _ _ _
   exact cost_before hk hx hy _ (-backA (Nat.lt_succ_self m)) (fun p=> by simp only [_root_.neg_apply,map_neg,neg_neg, Path.equal0]) _ _ _ _

omit hx hy hk

theorem directs_fact (p : Bool) (A:QP)(q:SectorP m×ℝ) : waveFact A (directs m p q)=forge A q.1 p := by
   have hu : waveFact A (slideA (Nat.lt_succ_self m) q)=waveFact A q.1:= by
      unfold waveFact; rw [onPlane_comp (Nat.le_succ m), show Cl _ (slideA (Nat.lt_succ_self m) q) =q.1 from congr_arg Prod.fst (Path.equal0 q (Nat.lt_succ_self m))]
   cases p; · unfold directs forge; simp only [Bool.false_eq_true,↓reduceIte,_root_.neg_apply]
              unfold waveFact; rw [map_neg, Tone.inverse, Tone.opp]; exact congr_arg (·⁻¹) hu
   exact hu

omit [FiniteDimensional ℝ E] in
theorem direction_formula (p:Bool)(A:QP)(X Y : Mob G)(l r : Touch G m E)(i j:Cfield G (m+1)) (q: SectorP m×ℝ) (x:E) :
    let W := Rock.move (G:=G) (E:=E) (Nat.le_succ m)
    brushWing (directs m p) K (rephase A X) Y (W l) (W r) i j (q,x) = waveFact A (net l x) *
       (forge A q.1 p * brushWing (directs m p) K X Y (W l) (W r) i j (q,x)) := by
   intro W; simp only [W,brushWing,oneCross,← moves,rephase_test, net_cons];
   unfold waveFact; rw [map_add,Tone.rightadd, show Tone.bill A (onPlane _ (directs m p q))=_ from directs_fact p A q, lifts_net, onPlane_comp (Nat.le_succ m),leftCl,sail_net]; ring

/-- Use two-sided separation estimates. `c i` a reciprocal wavelength, a
positive fraction. Unequalities used only inside the strongly separated shell. -/
structure Outpost (A:I→QP) (c:I→ℝ) : Prop where
   pos i: 0<c i
   scala i: c i ≤ 1
   payHigh : ∃ β:ℝ, 0< β ∧ ∀ i, ‖A i‖ ≤ β / c i
   payLow : ∃ β:ℝ, 0< β ∧ ∀ i, β / c i ≤ ‖A i‖

variable {g:I→(SectorP m×ℝ)×E→ℂ}
variable (h: Outpost P c)
omit [FiniteDimensional ℝ E] in
theorem forge_peak (A:QP) (m : ℕ) (p:Bool) : Peak (fun q:SectorP m=> forge A q p) :=
   ⟨fun _=> (Tone.bill_norm _ _).le, ((sailor _).shore).comp (onPlane _).continuous⟩
include h
omit [FiniteDimensional ℝ E] in
theorem outposts (hf : quiet ξ g a) (p:Bool) (k:ℕ) : quiet ξ (fun i=> stripeFourier (Px m) (fun q=> forge (P i) q p) (g i))
    (fun i=> a i * c i^k) := by
   obtain ⟨β,hβ,hp⟩:= h.payLow; let P'(i:I): QP := if p then P i else -P i;
   have ht (i) : β / c i ≤ ‖P' i‖ := by unfold P'; split <;> simpa using hp i
   choose H hv hH using (fun i=> Fiddle.flare (div_pos hβ (h.pos i)) (ht i)); let L(i:I):= Left (Nat.zero_le m) (H i); let S:= (1+‖Left (Nat.zero_le m)‖)*π/β; have hs :0< S:= by unfold S; positivity
   have hL i : ‖L i‖ ≤ S*c i:= calc
       _ ≤ ‖Left (Nat.zero_le m)‖ * ‖H i‖:= ContinuousLinearMap.le_opNorm ..
       _ ≤ (1+‖Left (Nat.zero_le m)‖) * (π/(β/c i)):= by
          gcongr
          · simp
          exact hH i
       _ = _:= by unfold S; rw [div_div_eq_mul_div]; ring
   refine amplified (Px m) hf (fun i=> forge_peak _ _ p) (fun i=>(hL i).trans (mul_le_of_le_one_right hs.le (h.scala i))) hs.le
     ?_ hL hs k
   intro i q; change Tone.bill (P' i) (onPlane m (q-L i))= -(Tone.bill (P' i) (onPlane m q)); unfold L; rw [map_sub,leftCl,lounge,hv]; ring

omit [FiniteDimensional ℝ E] in
-- `quiet` take external phase (cost could lose order at small length; use raised inputs).
theorem pinExtern {f : I→ℝ×E→ℂ} (W : Touch G m E) (hp : ∀ k:ℕ, quiet ξ f (fun i=> a i*c i^k)) (n : ℕ) :
    quiet ξ (fun i p=> waveFact (P i) (net W p.2) * f i p) (fun i=> a i*c i^n) := by
   intro k; obtain ⟨A,hA,hP⟩:= h.payHigh
   let U:= Arc.path ξ; let V : (ℝ×E)→L[ℝ] QP := onPlane _ ∘L net W ∘L ContinuousLinearMap.snd ℝ ℝ E
   have he:=pulseCost (K:=U.slow fun _=> Set.univ) (S:=U) (f:=f) (g:=fun i (p:ℝ×E)=> a i / U.weight i p.1^k)
     (V:=P) V (fun j=> (by simp_rw [div_mul_eq_mul_div]; exact hp j k)) h.pos h.scala ⟨A,hA,0,fun i p _=> by simpa [U,div_eq_mul_inv] using hP i⟩ n
   simp_rw [div_mul_eq_mul_div] at he
   exact he

include hk hx hy

theorem wingFourier (k : ℕ) (W : Touch G m E) (p:Bool) : quiet ξ
    (fun i=> carpet (Px m) (fun q: (SectorP m×ℝ)×E=> cutTree K (rephase (P i) (X i)) (Y i) (directs m p q.1) (Arts.lift (Nat.le_succ m) (sail W q.2))))
    (fun i=> (a i*b i) * c i^k) ∧ ∀ i (y:ℝ×E), Integrable (fun q=> cutTree K (rephase (P i) (X i)) (Y i) (directs m p (q,y.1)) (Arts.lift (Nat.le_succ m) (sail W y.2))) (Px m) := by
   classical
   let d:=Nat.le_succ m
   let U i:=(X i); let V i:= rephase (P i) (U i); let W'(l r:Touch G m E)(j j':Cfield G (m+1))(t:I):=
      brushWing (directs m p) K (V t) (Y t) (Rock.move d l) (Rock.move d r) j j'
   let P0(i:I)(j:ℝ×E) (q:SectorP m):= cutTree K (V i) (Y i) (directs m p (q,j.1)) (Arts.lift d (sail W j.2))
   have h_sf (l r:Touch G m E)(j j':Cfield G (m+1))(i:I)(y:ℝ×E) : Integrable (fun q:SectorP m=> W' l r j j' i ((q,y.1),y.2)) (Px m):= by
      simp only [W',U,V, direction_formula];
      exact ((stripe_major (Px m) (directCost hk hx hy p l r j j') (fun i=> forge_peak (P i) _ p) i).values y).const_mul _
   let f(l r:Touch G m E)(j j':Cfield G (m+1))(t:I) := carpet (Px m) (W' l r j j' t);
   have hh(l r:Touch G m E)(j j') : quiet ξ (f l r j j') (fun i=> a i*b i*c i^k) := by
      unfold f W' V U d carpet; simp_rw [direction_formula, integral_const_mul];
      exact pinExtern (a:=a*b) h l (fun v=> outposts h (directCost hk hx hy p l r j j') p v) k
   have he : ∀ i (y:ℝ×E), Integrable (P0 i y) (Px m) ∧ carpet (Px m) (fun q: (SectorP m×ℝ)×E=> cutTree K (V i) (Y i) (directs m p q.1) (Arts.lift (Nat.le_succ m) (sail W q.2))) y = scatter (field parity) W (fun l r=> ∑ j,∑ j', f l r j j' i y):= by
       intro i y; let X (q:SectorP m)(l r:Touch G m E):= ∑ j,∑ j',W' l r j j' i ((q,y.1),y.2);
       have ht (q:SectorP m): P0 i y q = scatter (field parity) W (X q) := by
           simp only [ P0,cutTree,Finset.sum_apply, Arts.scatter_up, sail_scatter]; refine scatter_congr _ _ _ _ fun l r _=> ?_; unfold X W' brushWing; simp_rw [← moves]
       have h_int(l r:Touch G m E) : Integrable (fun q=> X q l r) (Px m):= by unfold X; exact integrable_finsetSum _ (fun j _=> integrable_finsetSum _ (fun j' _=> h_sf l r j j' i y))
       constructor; · unfold P0; change Integrable (P0 i y) _; rw [funext ht]; exact (scatter_integral (f:=X) (Px m) (field parity) W (fun l r _=> h_int l r)).1
       change (∫ q,P0 i y q ∂Px m)=_; simp_rw [ht]; rw [(scatter_integral (f:=X) (Px m) (field parity) W (fun l r _=> h_int l r)).2];
       refine scatter_congr _ _ _ _ (fun l r _=>?_); unfold X; rw [integral_finsetSum _ (fun j _=>integrable_finsetSum _ (fun j' _=> h_sf l r j j' i y))];
       exact Finset.sum_congr rfl (fun j _=> integral_finsetSum _ (fun j' _=> h_sf l r j j' i y))
   refine ⟨?_,fun i y=> (he i y).1⟩
   change quiet _ (fun i=> carpet _ (fun q: (SectorP m×ℝ)×E=> cutTree K (V i) (Y i) (directs m p q.1) (Arts.lift (Nat.le_succ m) (sail W q.2)))) _
   simp_rw [fun i=> funext (fun y=> (he i y).2)]
   have h_u i : 0≤ a i*b i*c i^k:= by have hh:= h.pos i; exact mul_nonneg (mul_nonneg (znon hx _) (znon hy _)) (by positivity)
   have hT : ∀ (W:Touch G m E) (q:I→ℝ×E→Shared (Mode (Cfield G m) (E→L[ℝ] SectorP m)) ℂ), (∀ l r, quiet ξ (fun i y=> q i y l r) (fun i=> a i*b i*c i^k))→ quiet ξ (fun i y=> scatter (field parity) W (q i y)) (fun i=> a i*b i*c i^k):= by
      intro W; induction W with
      | nil=> exact fun q h=> h [] []
      | cons i w ih=> intro q h; exact ih _ (fun l r=> (h (i::l) r).add ((h l (i::r)).L (ContinuousLinearMap.mul ℝ ℂ _)))
   exact hT W _ (fun l r=> tranquil _ (fun j _=> tranquil _ (fun j' _=> hh l r j j') h_u) h_u)

variable (hp : ∀ i, Sturdy false (X i)) (hP : ∀ i, Sturdy false (Y i)) (hw : Ruddy false K)
  (he : reverseF K) (hB : closedF K false)
-- guard the exponent of the radial integration
variable (hr : ∀ i,S i∈Town) (hs : ∀ i, 2*(S i).re+1≤ (n:ℝ))
   (ht : scaleC ξ v (fun i=> ‖tenorK (S i) (y i)‖))
include hp hP hw he hB hr hs ht

theorem pose (k : ℕ) : fell ξ (fun i=> v i * (a i*b i*c i^k)) (fun i=> pinned K (S i) (y i) (P i) (X i) (Y i)):= by
   intro m E _ _ _ w
   let f(i:I):= cutWing K (rephase (P i) (X i)) (Y i) w
   have he' (i:I): Sweeping (f i):= cutSweep w ⟨hk,hw⟩ hB he (form_rephase ⟨Rock.fee hx i,hp i⟩ _) ⟨Rock.fee hy i,hP i⟩
   have hxy (i:I): fieldVal (pinned K (S i) (y i) (P i) (X i) (Y i) m) w = tenorK (S i) (y i) • swoop (S i) (Px m) m (f i) := pin_chart w ⟨hk,hw⟩ hB he ⟨Rock.fee hx i,hp i⟩ ⟨Rock.fee hy i,hP i⟩ (S i) (P i) (y i)
   let g (p:Bool)(i:I)(x : (SectorP m×ℝ)×E):= cutTree K (rephase (P i) (X i)) (Y i) (directs m p x.1) (Arts.lift (Nat.le_succ m) (sail w x.2))
   have hu (i) : f i=g true i + g false i:= rfl
   have hG (p : Bool) (i:I) (y:ℝ×E) : Integrable (fun q=>g p i ((q,y.1),y.2)) (Px m) := by
      exact (wingFourier hk hx hy h 0 w p).2 i y
   have h_g : quiet ξ (fun i=> carpet (Px m) (f i)) (fun i=>a i*b i*c i^k):= by
     simp_rw [show ∀ i, carpet (Px m) (f i)=carpet (Px m) (g true i)+carpet (Px m) (g false i) from fun i=> by rw [hu]; exact funext fun x=> integral_add (hG true i x) (hG false i x)]
     exact (wingFourier hk hx hy h k w true).1.add (wingFourier hk hx hy h k w false).1
   have hC : veg ξ (fun i=> swoop (S i) (Px m) m (f i)) (fun i=>a i*b i*c i^k):= by
      convert! core h_g (fun i=> mirror_r (Px m) (he' i).2) m (shade_cloud hr hs) using 1; simp
   simp_rw [hxy]; exact Costs.mul (at_rate ht) hC
end YM.MS.ScaleForest
