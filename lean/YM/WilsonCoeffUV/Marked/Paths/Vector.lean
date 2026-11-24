import YM.WilsonCoeffUV.Marked.Paths.Root
import YM.WilsonCoeffUV.Reclosure.Paths.SignedPackets
import YM.WilsonCoeffUV.Marked.Step.Exponential
import Mathlib.Analysis.LocallyConvex.SeparatingDual
/-! Exact scalarized reading of a vector mark atom.
 Periodic analytic probes include all knot aliasing on Side n. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Rolls
open Gauge Power PowerSeries Matrix Filter Lattice Laurent Exterior Precision Wilson RG Tree Bloch Stationary
open Function Blue Bank Fountain Soil Source Source.Drops Labels Cosmos Planned.PrimaryIntegral295 Place Carrier Bank.Carp Bank.Mosaic Bank.Mosaic.Near
open scoped Topology ContDiff BigOperators Classical
open Work.F03
variable {G:Gauge}{n:Side}{k h r t i j e:ℕ}{s A B:ℝ}
variable {V W I:Type}[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]

omit [CompleteSpace V] in
lemma probe {x y:V}(h:∀ L: V→L[ℝ]ℝ,L x=L y):x=y:= by apply (SeparatingDual.eq_iff_forall_dual_eq (R:=ℝ)).mpr; exact h

structure Comet (G:Gauge)(V:Type)(r:ℕ) where
    sl : Fin r→ Slot
    wage : Stationary.Ink G r→ V
-- colored payment including rank 0
def dip (C:Comet G V r)(L: V→L[ℝ]ℝ): Atom G r:= ⟨C.sl,L ∘ C.wage⟩
def rayOne (C:Comet G V r)(i:Stationary.Ink G r): Atom G r:= ⟨C.sl, Pi.single i 1⟩
def integerP (C:Comet G V r)(s:ℝ):ℝ := ∑ i, ‖C.wage i‖*(rayOne C i).budget s
def shadeStar (C:Comet G V r): Prop:=∀ L: V→L[ℝ]ℝ,(dip C L).Invariant
omit [CompleteSpace V] in
lemma dip_surge (C:Comet G V r)(L: V→L[ℝ]ℝ)(w) : (dip C L).poly w=∑ i,L (C.wage i)*(rayOne C i).poly w:=by
    unfold Atom.poly; refine Finset.sum_congr rfl fun i _=>?_ ; congr 1; symm; rw [Finset.sum_eq_single i]; simp [rayOne]
    · intro j p h; rw [show (rayOne C i).coeff j=0 from Pi.single_eq_of_ne h _,zero_mul]
    simp
-- evaluation rank-k canonical payment

def sapR (C:Comet G V r)(n:Side)(k:ℕ): Ten V (Woods G n) k:=fun x=> ∑ i, rye (meter (rayOne C i) (0:Site n)) k x • C.wage i
def august (C:Comet G V r)(k:ℕ): Ten V (YForest G) k:=fun x=> ∑ i, signal (rayOne C i) k x • C.wage i
omit [CompleteSpace V] in
lemma sap_view (C:Comet G V r)(n:Side)(k:ℕ)(x)(L: V→L[ℝ]ℝ): L (sapR C n k x) = rye (meter (dip C L) (0:Site n)) k x := by
    let F (i:Stationary.Ink G r):Lawn (Woods G n)→ℝ:= meter (rayOne C i) 0
    let X i:= L (C.wage i) • F i; have he i: Green (X i):= (meter_hot ..).contDiffAt.const_smul (L (C.wage i))
    have hp: meter (dip C L) (0:Site n)= ∑ i,X i:=by funext x; rw [Finset.sum_apply]; exact dip_surge ..
    rw [hp,rye_scoped (fun i _=>he i),Finset.sum_apply,sapR,map_sum]; refine Finset.sum_congr rfl (fun u _=>?_); rw [L.map_smul]; unfold X F; rw [rye];
    rw [rye,show _ from iteratedFDeriv_const_smul_apply (x:=0) (a:=L (C.wage u)) ((meter_hot (rayOne C u) (0:Site n)).contDiffAt.of_le (le_top (a:=((k:WithTop ℕ∞)))))]; rw [_root_.smul_apply]; simp only [smul_eq_mul]; ring
-- pricing
omit [CompleteSpace V] in
lemma augments (C:Comet G V r)(k:ℕ)(v:Stationary.Ink G r)(h:0<s): Cork Bank.terrain 0 (steep s) (‖C.wage v‖ * ((rayOne C v).budget s * flour G (steep s) r k)) (fun x=> signal (rayOne C v) k x • C.wage v):=by
    have hp:=signal_price (rayOne C v) h k; refine ⟨mul_nonneg (norm_nonneg _) hp.1,fun i=>?_⟩; rw [norm_smul]; exact (mul_le_mul_of_nonneg_right (hp.2 i) (norm_nonneg _)).trans_eq (by ring)
omit [CompleteSpace V] in
lemma aug_price (C:Comet G V r)(h:0<s)(k:ℕ): Cork Bank.terrain 0 (steep s) (integerP C s * flour G (steep s) r k) (august C k):=by
    let L i:= fun x=> signal (rayOne C i) k x • C.wage i; have he:= Cork.sum (s:=Finset.univ) (P:=L) (fun i _=> augments C k i h); rw [show august C k= (∑ i,L i) from funext fun x=>by rw [Finset.sum_apply]; rfl]; apply he.cost; unfold integerP; rw [Finset.sum_mul]; simp only [mul_assoc, le_refl]
omit [NormedSpace ℝ V] in
lemma plume_spurs {α:Type}{F:α→Ten V (YForest G) k}{X:α→ℝ}(S:Finset α)(p:∀ i∈S,Cork Bank.terrain 0 s (X i) (F i))(h:0<s) (n:Side): plume (∑ i∈S,F i) n=∑ i∈S, plume (F i) n:=by
    induction S using Finset.induction_on with
    | empty=> simp [plume_zero]
    | @insert i S hi ih=> have ht j hj:=p j (Finset.mem_insert_of_mem hj); rw [Finset.sum_insert hi, Finset.sum_insert hi, plume_add (p i (Finset.mem_insert_self ..)) (Cork.sum ht) h h n, ih ht]
lemma aug_plume (C:Comet G V r)(k:ℕ)(n): plume (august C k) n=sapR C n k:=by
    let L i:= fun x=> signal (rayOne C i) k x • C.wage i; have h:0<steep 1:=by unfold steep; norm_num
    funext x; rw [show august C k= ∑ i,L i from funext fun x=> by rw [Finset.sum_apply]; rfl, plume_spurs (X:=fun i=> ‖C.wage i‖*((rayOne C i).budget 1*flour G _ r k)) (F:=L) Finset.univ (fun i _=> augments C k i (s:=1) one_pos) h n, Finset.sum_apply]
    apply Finset.sum_congr rfl; intro i _; let V':ℝ→L[ℝ]V:= ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (C.wage i)
    change plume (V' ∘ (signal (rayOne C i) k)) _ _=_; rw [plume_map _ (signal_price _ one_pos _) h V' n,Function.comp_apply,signal_seed]; rfl
-- grade shift shell. terms g^(e-r) lifted.

def moved {U:Type*}(r e:ℕ)(A:Gen V U):Pal V U:=fun i=> if e≤ i then shine (A (r+(i-e))) else 0
omit [NormedSpace ℝ V] [CompleteSpace V] in
lemma movesCount {U:Type*}(A:Gen V U)(h:r≤k+e) :shellK k (moved r e A):=by
   intro i j hv; unfold moved; split; · rw [shine_dark (by omega :r+(i-e)≠j)]
   rfl

def volumeR (A:Comet G V r)(e:ℕ): Era G V :=(fun n=> moved r e (sapR A n), moved r e (august A))
omit [CompleteSpace V] in
lemma volume_probe (C:Comet G V r)(e:ℕ)(n:Side)(L:V→L[ℝ]ℝ) : ply L.toLinearMap ((volumeR C e).1 n) =fun i=> if e≤ i then sprig (meter (dip C L) (0:Site n)) r (i-e) else 0:=by
    funext i j x; rw [ply_v]; unfold volumeR; simp only [moved]; split
    next t=> by_cases H:r+(i-e)=j
             · subst j; simp only [sprig, shine_lit]; exact sap_view ..
             · simp only [sprig,shine_dark H]; exact map_zero _
    exact map_zero _
lemma aug_auth (X:Comet G V r)(v:shadeStar X)(p:r≤k+e): Auth k (volumeR X e):=by
    have hx :0 < steep 1:=by unfold steep; norm_num
    let T:= volumeR X e
    have ht n L : flash (ply (L:V→L[ℝ]ℝ).toLinearMap (T.1 n))=PowerSeries.X^e * flash (sprig (meter (dip X L) (0: Site n)) r):=by
       unfold T; rw [volume_probe]; ext1 i; rw [coeff_X_pow_mul']; unfold Blue.flash; simp only [coeff_mk]; split; rfl; simp [totalR]
    refine ⟨fun i k=>?_,fun i=>movesCount (sapR X i) p,fun n i j q x=>?_,fun n=>certify (fun L: V→L[ℝ]ℝ=>L.toLinearMap) (fun _ _ h=>probe h) _ (movesCount (sapR X n) p) (fun L=>?_)⟩
    · unfold volumeR; simp only [moved]; split
      next t=> by_cases h:r+(i-e)=k; · subst k; simp_rw [shine_lit,←aug_plume]; exact caisson (aug_price X one_pos _) hx
               simp_rw [shine_dark h]; exact Bends.zero
      exact Bends.zero
    · apply probe; intro L; let A:= meter (dip X L) (0:Site n); change ply L.toLinearMap ((volumeR X e).1 n) i j (x ∘ q)=ply L.toLinearMap ((volumeR X e).1 n) i j x; rw [volume_probe]; dsimp only; split
      next p=> exact (sprig_pure A (meter_hot ..).contDiffAt r _ j) q x
      rfl
    change rollTest (flash (ply L.toLinearMap (T.1 _))) (flash (ply L.toLinearMap (T.1 _))) 1 0; rw [ht]; intro Z I y U W k; rw [map_mul,map_pow,train_X,map_mul,map_pow,train_X,meter_ward (dip X L) (v L) n k]
lemma aug_plane (A:Comet G V r)(e k t:ℕ)(n:Side): (volumeR A e).1 n k t= plume ((volumeR A e).2 k t) n:=by
    unfold volumeR; simp only [moved]; split
    next i=> by_cases h:r+(k-e)=t; · subst t; rw [shine_lit,shine_lit]; exact (aug_plume ..).symm
             rw [shine_dark h,shine_dark h,plume_zero]
    exact Eq.symm (plume_zero _)
omit [CompleteSpace V] in
lemma volume_price (X:Comet G V r)(h:0<s)(i j k): Cork Bank.terrain 0 (steep s) (integerP X s*flour G (steep s) r k) ((volumeR X i).2 j k):=by
    have he:= aug_price X h k; change Cork _ _ _ _ (moved r i (august X) j k); unfold moved; split
    next u=> by_cases v:r+(j-i)=k; · rw [v,shine_lit]; exact he
             rw [shine_dark v]; exact Cork.zero.cost he.1
    exact Cork.zero.cost he.1
end YM.WilsonCoeffUV.Mer.Rolls
