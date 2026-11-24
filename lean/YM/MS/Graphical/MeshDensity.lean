import YM.MS.Graphical.PinPhases
import YM.MS.Graphical.WingLink

/-!
# Estimating the multi-pin loop with the large-frequency gain in the cross term

Key estimate for the absence of any additional counterterm for the join of two
separated marks in this prescription; all powers of small scale are available
(running the loop integral with z in a compact in `Town`).
-/

set_option autoImplicit false
noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Real Metric
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Pearl Train Signal Book Convolve Garment.Wick Dock
open scoped Topology ContDiff
variable {I E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {s : I→ℝ}
    {G : Gauge} {a b c : I → ℝ} {x : Tone.QP} {Z : I → ℂ} {f g : I→Mob G} {U : I→ Rip G} {m n : ℕ}

private def evalPair (K : E →L[ℝ] SectorP n) (W V : Touch G n Y) (U : I→ Rip G)
    (f g : I→ Mob G) (i : I) (p : E×Y) :=
    ∑ a:Cfield G n,∑ b:Cfield G n,pinEdge (f i) (g i) (U i) a b (K p.1) (sail W p.2) (sail V p.2)

variable (A : E →L[ℝ] SectorP n) (L : SectorP n→L[ℝ] E) (hL : ∀ i, L (A i)=i)
variable (h : fell 0 a f) (hp : fell 0 b g) (hU : rib 0 c U) (hc : ∀ i, 0≤ c i)
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ Y]

include hL h hp hU hc
lemma mesh_both_strength (w v : Touch G n Y) :
    quiet 0 (evalPair A w v U f g) (fun i=>c i*a i*b i) := by
  unfold evalPair; have h' i: 0 ≤ c i* a i*b i:= mul_nonneg (mul_nonneg (hc i) (znon h i)) (znon hp i)
  refine tranquil _ (fun i _=> tranquil _ (fun j _=>?_) h') h'
  let Aw:= A ∘L ContinuousLinearMap.fst ℝ E Y; let Hw:= ContinuousLinearMap.snd ℝ E Y
  let P:=(i,Aw)::Wire.lift w Hw; let Q:=(j,-Aw)::Wire.lift v Hw
  have htp:= ((Line.rapid (F:=Y) (ride_peak (hU _ i j) hL)).mul (h n (E×Y) P)).mul
        (hp n (E×Y) Q)
  convert! htp.L (ContinuousLinearMap.mul ℝ ℂ (cross (parity j) (degree (field Landau.parity) w))) using 1
  ext x p; obtain ⟨p,q⟩:=p
  simp only [pinEdge,P,Q,fieldVal,sail_degree,sail_cons,lift_sail,Hw,show (ContinuousLinearMap.snd ℝ E Y) (p,q)=q from rfl,
    ContinuousLinearMap.mul_apply', Aw, ContinuousLinearMap.comp_apply,show (ContinuousLinearMap.fst ℝ E Y) (p,q)=p from rfl,
    _root_.neg_apply]
  ring
omit hL

private def spins (h : m < n) (u : Tone.QP) (U : Rip G) (F H : Mob G) (w v : Touch G m E)
    (x : WingDomain m E) := waveSector h u x.1.2 x.1.1 F H U (sail w x.2) (sail v x.2)

omit h hp hU hc in
lemma separate_phase (U : Tone.QP) (i : SectorP m) : phase m U (-i)=phase m (-U) i:= by
  unfold phase; rw [map_neg,Tone.opp,Tone.inverse]

variable (hv : ∀ i,0<s i)(ht: ∀ i,s i≤1) (hx : x≠0)
include hv ht hx
lemma separation (hn : m<n) (w v : Touch G m E) (k : ℕ) :
    (∀ i, ∀ s' : ℝ, ∀ x' : E,
       Integrable (fun p => spins hn ((s i)⁻¹ • x) (U i) (f i) (g i) w v ((p,s'),x')) (Px m)) ∧
    quiet 0 (fun i=> carpet (Px m) (spins hn ((s i)⁻¹ • x) (U i) (f i) (g i) w v))
       (fun i=> c i*a i*b i*s i^k) := by
  let A:= slideA hn; let L:=backA hn
  let X:= evalPair A (move hn.le w) (move hn.le v) U f g
  let Y:= evalPair (-A) (move hn.le w) (move hn.le v) U f g
  let P(i:I):= (s i)⁻¹ • x; let Q(i:I):=(s i)⁻¹ • (-x)
  have hK (i:I) (p : SectorP m) (t : ℝ) (k : E) : spins hn (P i) (U i) (f i) (g i) w v ((p,t),k) =
      phase m (P i) (net w k)* (phase m (P i) p*X i ((p,t),k) + phase m (Q i) p* Y i ((p,t),k)) := by
    unfold spins waveSector X Y A evalPair P Q; rw [smul_neg]; simp_rw [sail_net,moves]; rw [separate_phase]; rfl
  let C i:= c i*a i*b i; have hA:quiet 0 X C:=mesh_both_strength A L (fun i=>equal0 i hn) h hp hU hc _ _
  have hB: quiet 0 Y C:=mesh_both_strength _ (-L) (by intro p; simp only [_root_.neg_apply,map_neg,neg_neg]; exact equal0 p hn) h hp hU hc _ _
  have hp (u : Tone.QP) : Osc.Peak (phase m u) := ⟨fun X=> (Tone.bill_norm ..).le,
    (Fiddle.bill_sm u).continuous.comp (Cl (Nat.zero_le m)).continuous⟩
  let R:= fourierPlane (Px m) X (fun i=>phase m (P i)); let S:=fourierPlane (Px m) Y (fun i=>phase m (Q i))
  have Hx i:=Osc.Vmajor (hp (P i)) (Arc.Q.Gmajor (Px m) hA i); have Hy i:=Osc.Vmajor (hp (Q i)) (Arc.Q.Gmajor (Px m) hB i)
  constructor
  · intro i t k; change Integrable (fun p => spins hn (P i) (U i) (f i) (g i) w v ((p,t),k)) (Px m)
    simp_rw [hK]; exact (((Hx i).values (t,k)).add ((Hy i).values (t,k))).const_mul _
  unfold carpet; change quiet 0 (fun i (p:ℝ× E)=> ∫ q, spins hn (P i) _ _ _ w v ((q,p.1),p.2) ∂Px m) _;
  simp_rw [hK,integral_const_mul];
  rw [show (fun (i:I) (p:ℝ×E) => phase m (P i) (net w p.2) * (∫ q, _ + _ ∂Px m))= _ from
      (show (fun i p=> _) = (fun (i:I) (p:ℝ×E)=> phase m (P i) (net w p.2)*(R i p+ S i p)) from
        funext fun i=>funext fun p=>congr_arg (phase m (P i) (net w p.2)* · ) (integral_add ((Hx i).values p) ((Hy i).values p)))]
  apply keeps hv ht x ((Cl (Nat.zero_le m)) ∘L ((net w) ∘L ContinuousLinearMap.snd ℝ ℝ E))
    (fun i=> (gains hv ht hA hx i).add (gains hv ht hB (neg_ne_zero.mpr hx) i)) k

/-- Finally, the actual falloff of the *integrals* of the joins. All powers in
small scale (0 < s ≤ 1), and uniform in any fixed z-compact. No interchange
with specializing to 4 dimensions is assumed. -/
theorem falloff_join {K : Set ℂ} (HK : IsCompact K) (HP : K ⊆ Town) (hz : ∀ i,Z i∈K)
    (hF : ∀ i, Sturdy false (f i)) (hH : ∀ i, Sturdy false (g i)) (hK : ∀ i, Ruddy false (U i))
    (hr : ∀ i, reverseF (U i)) (hk : ∀ i, closedF (U i) false) (y : ℝ) (k : ℕ) :
    fell 0 (fun i=> c i*a i*b i*s i^k) (fun i=>wickJoin ((s i)⁻¹ • x) (U i) (Z i) y (f i) (g i)) := by
  intro m E _ _ _ w
  let A i:= c i*a i*b i*s i^k; let n:= m+1; let X i := (s i)⁻¹ • x; let T (i:I):= Z i-n
  let M i:= connectedWing (X i) (f i) (g i) (U i) (Z i) w
  let τ(i:I) (p:SectorP m)(t:ℝ)(x:E)(r:ℕ)(he:m<r) :=
      scatter (field Landau.parity) w (fun l v=>spins he (X i) (U i) (f i) (g i) l v ((p,t),x))
  let S (r:ℕ)(he:m<r)(i:I) (p:ℝ× E) := ∫ q, τ i q p.1 p.2 r he ∂Px m
  have he (r:ℕ)(he:m<r) (i:I)(p:ℝ× E)(l v:Touch G m E) :=
      (separation (x:=x) h hp hU hc hv ht hx he l v k).1 i p.1 p.2
  have HS (r:ℕ)(hr:m<r)(i:I)(p:ℝ × E) :=
      scatter_integral (Px m) (field Landau.parity) w
          (f:=fun q l v=> spins hr (X i) (U i) (f i) (g i) l v ((q,p.1),p.2))
          (fun i' j _=>he r hr i p i' j)
  have hh (r:ℕ)(hr:m<r): quiet 0 (S r hr) A:= by
    unfold S τ; simp_rw [(HS r hr _ _).2]; exact quiet_scatter w
      (fun l r _=> (separation h hp hU hc hv ht hx hr l r k).2)
  have hZ : ∀ i t, carpet (Px m) (M i) t = S n (Nat.lt_succ_self m) i t+
      (T i)*(S (n+1) (by unfold n; omega) i t-S n (Nat.lt_succ_self m) i t) := by
    intro i t; unfold carpet S
    have h0 (p:SectorP m): M i ((p,t.1),t.2) =
       τ i p t.1 t.2 n (Nat.lt_succ_self m)+(T i)*(τ i p t.1 t.2 (n+1) (by unfold n; omega)-τ i p t.1 t.2 n (Nat.lt_succ_self m)):= by
      obtain he := wick_tensors (Z i) (X i) t.1 p w t.2 (hK i) (hF i) (hH i) (hr i) (hk i)
      simp_rw [sail_scatter] at he; exact he
    simp_rw [h0]; have ht:= (HS _ (Nat.lt_succ_self m) i t).1; have hu:= (HS _ (show m<n+1 by unfold n; omega) i t).1
    refine (integral_add ht ((hu.sub ht).const_mul (T i))).trans (congr_arg₂ (·+·) rfl ?_)
    rw [integral_const_mul]; exact congr_arg (T i*·) (integral_sub hu ht)
  have H (f : ℂ→ℂ) (h : ContinuousOn f K) : scaleC 0 1 (fun i=> ‖f (Z i)‖) := by
    obtain ⟨R,hR⟩:= (HK.image_of_continuousOn h.norm).bddAbove
    exact ⟨max 1 R, lt_max_of_lt_left zero_lt_one,0,fun i p _=> by
       simpa using (hR (mem_image_of_mem _ (hz i))).trans (le_max_right 1 R)⟩
  have hy : quiet 0 (fun i=>carpet (Px m) (M i)) A:= by
    rw [show (fun i=>carpet (Px m) (M i))=_ from funext (fun i=>funext (hZ i))];
    apply (hh _ (Nat.lt_succ_self m)).add;
    simpa only [Pi.one_apply,mul_one] using (Cquiet (u:=T) ((hh _ (show m<n+1 by unfold n; omega)).sub
       (hh _ (Nat.lt_succ_self m))) (H (fun z=>z-n) (show ContinuousOn _ _ from Continuous.continuousOn (by fun_prop))))
  have he(i:I): Reflect (carpet (Px m) (M i)):= mirror_r _ (connected_reflect (X i) (hF _) (hH _) (hK _) _ _)
  let V (z:ℂ) := 2*z.re+1; obtain ⟨R,hR⟩:= (HK.image (show Continuous V from by unfold V; fun_prop)).bddAbove
  obtain ⟨j,hj⟩:= exists_nat_ge R; obtain hy:= core hy he m (shade_cloud (Z:=Z) (fun i=>HP (hz i))
        (fun i=>(hR (mem_image_of_mem _ (hz i))).trans hj));
  have ht: veg 0 (fun i=>swoop (Z i) (Px m) m (M i)) A := by convert hy using 1; all_goals first | rfl | (ext; simp)
  have he (i:I)(p:E) : fieldVal (wickJoin (X i) (U i) (Z i) y (f i) (g i) m) w p=
      tenorK (Z i) y * swoop (Z i) (Px m) m (M i) p :=
    Eq.symm (connected_integral _ _ w p ⟨Rock.fee h i,hF i⟩ ⟨Rock.fee hp i,hH i⟩
      ⟨fun m a b=>fastline (hU m a b) i,hK i⟩ (HP (hz i)))
  change veg 0 (fun i=> fieldVal (wickJoin (X i) (U i) (Z i) y (f i) (g i) m) w) A
  rw [show (fun i=> fieldVal _ w)=_ from funext (fun i=>funext (he i))]; convert!
      Costs.mul (at_rate (E:=E) (H (fun z=>tenorK z y) (fun i hi=> (tenor_hol y i (HP hi)).continuousAt.continuousWithinAt))) ht using 1
  ext; simp
end YM.MS.Graphical
