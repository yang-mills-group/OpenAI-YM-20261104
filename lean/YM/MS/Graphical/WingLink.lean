import YM.MS.Graphical.PinWing

/-!
# The actual edges in the multi-pin Arc measure integrand

Give formula on integer-dimensional open sectors (for any complex z),
including ghost reflection sign. Useful also in the separated ghost test.
The continuous z-dependence of this contraction is just the extrapolation
in `wick_tensors`: no necessity here for simplifying to e.g. isotropic
physical tensor inputs.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Real Metric
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Pearl Train Signal Book Convolve Garment.Wick Dock
open scoped Topology ContDiff
variable {G : Gauge} {E J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F H : Mob G} {U : Rip G} {K : Ridge G 0} {z : ℂ} {m n : ℕ}

def pinEdge (F H : Mob G) (K : Rip G) (a b : Cfield G m) (p : SectorP m) (l r : Legs (Shore G m)) :=
  K _ a b p * (cross (parity b) (degree (field Landau.parity) l) * F _ ((a,p)::l)) * H _ ((b,-p)::r)

lemma flipEdge (hk : reverseF U) (p : SectorP m) (a b : Cfield G m) (l r : Legs (Shore G m)) :
    pinEdge F H U b a (-p) l r=U _ a b p *
      (cross (parity a) ( (parity b).xor (degree (field Landau.parity) l)) * F _ ((b,-p)::l)) * H _ ((a,p)::r) := by
  unfold pinEdge; rw [hk m b a p, cross_right (parity a) (parity b), neg_neg, cross_comm (parity a) (parity b)]; ring

/-- Shell allocated in both orientations, no phase. Use
with half-line `U`. We use reversal here (`reverseF` on the edge kernel),
keeping the parity sign from reversing. No even-row assumption on the
components (placing smallest source on the **right** fixes order). -/
lemma crossReading (h : reverseF U) (hx : closedF U false) (F H : Mob G) (p : SectorP m)
    (w : Legs (Shore G m)) :
    link (trc (U m) p) false (field Landau.parity) (F m) (H m) w =
      scatter (field Landau.parity) w (fun l r=> ∑ i:Cfield G m,∑ j:Cfield G m,
        (pinEdge F H U i j p l r+pinEdge F H U i j (-p) l r)) := by
  let P:= trc (U m) p; let L (i j : Cfield G m) (l r : Legs (Shore G m)):=
    pinEdge F H U i j p l r+pinEdge F H U j i (-p) l r
  let Q:=allocate (field Landau.parity) w (R:=ℂ)
  have he (i j : Cfield G m) : U _ i j p • link (diffPair (i,p) (j,-p)) false (field Landau.parity)
        (F _) (H _) w = Q (L i j) := by
    unfold L; by_cases ht : U _ i j p=0
    · simp_rw [flipEdge (F:=F) h p i j,pinEdge,ht,zero_mul,add_zero]; exact Eq.trans (zero_smul ..) Q.map_zero.symm
    rw [split_line i j _ _ (hx _ i j p ht),show U _ i j p • scatter _ w _ = Q _ from (Q.map_smul (U _ i j p) _).symm]
    apply congr_arg Q; ext v x; simp_rw [Pi.smul_apply,smul_eq_mul,flipEdge h p i j,pinEdge]; ring
  unfold trc; simp_rw [link_sum,link_scale,Finset.sum_apply,Pi.smul_apply,he,← map_sum]
  apply congr_arg Q; ext l r; simp only [L,Finset.sum_apply,Finset.sum_add_distrib]; congr 1; exact Finset.sum_comm

lemma phase_dance (x : Tone.QP) (t : ℝ) (u : SectorP m) (h : m < n) :
    phase n x (slideA h (u,t)) = phase m x u:= by
  have ht := congr_arg Prod.fst (equal0 (u,t) h); change Cl h.le (slideA h (u,t))=u at ht
  unfold phase; congr 1
  change Cl (Nat.zero_le n) _ = _
  rw [show ∀ p, Cl (Nat.zero_le n) p=Cl (Nat.zero_le m) (Cl h.le p) from fun _=>rfl, ht]

-- allocation with phases factored in BOTH allowed orientations. One single
-- trace read includes the difference of two extrapolated integer-sector reads
-- with z-dependent coefficient.

def waveSector (h : m<n) (a : Tone.QP) (t : ℝ) (p : SectorP m) (F H : Mob G) (U : Rip G)
    (l r : Legs (Shore G m)):=
  let u:=slideA h (p,t)
  let e (u : SectorP n) := ∑ i:Cfield G n, ∑ j:Cfield G n, pinEdge F H U i j u (Arts.lift h.le l) (Arts.lift h.le r)
  phase m a (net l) * (phase m a p * e u + phase m a (-p) * e (-u))

lemma integerSector_payment (u : Tone.QP) (x : ℝ) (h : m+1≤n) (K : SectorP m) (W : Touch G m E) (p : E)
    (hU : Ruddy false U) (hF : Sturdy false F) (hH : Sturdy false H) (hr : reverseF U) (hc : closedF U false) :
    connectedWing u F H U (n:ℂ) W ((K,x),p) =
      scatter (field Landau.parity) (sail W p) (waveSector (show m<n by omega) u x K F H U) := by
  let a := bring u F; let v:= sail W p; obtain hf:=bring_sturdy u hF
  let q:= slideA (show m<n by omega) (K,x); let hs:= Nat.lt_succ_self m; let ht:m≤n:=by omega
  have he (f : Mob G) (hf : Sturdy false f) (l : Legs (Shore G m)) :
      Wtr (n:ℂ) U f (slideA hs (K,x)) (Arts.lift (Nat.le_succ m) l)=trc (U n) q (f n) (Arts.lift ht l) := by
    rw [tallyN hf hU h, slide_ext hs h, lifts_link]
  have hW : connectedWing u F H U (n:ℂ) W ((K,x),p)=
      link (trc (U n) q) false (field Landau.parity) (a n) (H n) (Arts.lift ht v):= by
    unfold connectedWing; change Wtr (n:ℂ) U (shuffleRows a H) (slideA hs (K,x)) _ - _ - _ = _
    rw [he _ (shuffle_sturdy hf hH),link,sign_id,Pi.sub_apply,Pi.sub_apply]
    simp_rw [scattered,scatter_up ht];
    unfold leftMesh rightMesh readWing pulls; dsimp only [a]; simp only [scattered,he (bring u F) hf, he H hH,hf.grows ht,hH.grows ht];  rfl
  have hph := phase_dance u x K (show m<n by omega)
  have he (z : SectorP m) (w : SectorP n) (hq : phase n u w=phase m u z)
      (i j : Cfield G n) (l r : Legs (Shore G m)) : pinEdge a H U i j w (Arts.lift ht l) (Arts.lift ht r) =
       phase m u (net l)*phase m u z*pinEdge F H U i j w (Arts.lift ht l) (Arts.lift ht r) := by
    unfold pinEdge a bring
    rw [net_cons, show ∀ p q, phase n u (p+q)= phase n u p*phase n u q from fun p q=>?_,
        hq, lifts_net,phase_up]
    · ring
    unfold phase; rw [map_add, Tone.rightadd]
  rw [hW, crossReading hr hc, scatter_up]
  apply scatter_congr; intro l r _
  simp only [waveSector];
  have hp : phase n u (-q) = phase m u (-K) := by
    unfold phase; rw [map_neg,map_neg,Tone.inverse,Tone.inverse]; exact congr_arg (fun x:ℂ=>x⁻¹) hph
  simp only [he K q hph, he (-K) (-q) hp, Finset.sum_add_distrib,
    ← Finset.mul_sum];
  change (_+_) = _ * (_*_+_*_); dsimp only [q]; ring

theorem wick_tensors (z : ℂ) (u : Tone.QP) (x : ℝ) (K : SectorP m) (W : Touch G m E) (p : E)
    (hU : Ruddy false U) (hF : Sturdy false F) (hH : Sturdy false H) (hr : reverseF U) (hc : closedF U false) :
    let A:= scatter (field Landau.parity) (sail W p) (waveSector (Nat.lt_succ_self m) u x K F H U)
    let B:= scatter (field Landau.parity) (sail W p) (waveSector (show m<m+1+1 by omega) u x K F H U)
    connectedWing u F H U z W ((K,x),p) = A+(z-(m+1:ℕ)) • (B-A) := by
  intro A B
  let a(c:ℂ) := connectedWing u F H U c W ((K,x),p)
  have hA : a (m+1:ℕ) = A:= integerSector_payment u x (le_refl (m+1)) K W p hU hF hH hr hc
  have hB : a (m+1+1:ℕ) = B:= integerSector_payment u x (Nat.le_succ (m+1)) K W p hU hF hH hr hc
  rw [← hA, ← hB]
  let V:= m+1; let h:= Nat.lt_succ_self m; let pρ:=slideA h (K,x)
  have hz (F : Mob G) : pulls h.le (Wtr z U F pρ) = pulls h.le (Wtr (m+1:ℕ) U F pρ)+
        (z-(m+1:ℕ)) • (pulls h.le (Wtr (m+1+1:ℕ) U F pρ)-pulls h.le (Wtr (m+1:ℕ) U F pρ)) := by
    rw [combo z]; rfl
  unfold a connectedWing leftMesh rightMesh; simp only [Pi.sub_apply, readWing];
  simp only [← readWing_eval, readWing]; dsimp only [pρ] at hz; simp only [hz,map_add,map_sub,map_smul,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  rw [hz (shuffleRows (bring u F) H)]
  simp only [Pi.add_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]; ring
end YM.MS.Graphical
