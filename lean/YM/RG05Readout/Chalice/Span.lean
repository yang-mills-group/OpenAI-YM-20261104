import YM.RG05Readout.Chalice.Elector
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Chalice
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {b k l:ℕ}{Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
open Pulse Extraction Extraction.Lease
open Push.RelayDifference
variable {D:Address.Rail C}

variable {f: Extraction.Order}

/-! A transcription at common origin: affordable → vetted literal against calibrated matrices, absorb a finite bank then same at ALL higher SBP orders on-demand. For low-weight planes repaint them further. -/
open Petals Petals.Kernel Bay Dash
/-!
# Separated real transcript smears.Wide support through every calibrated chart within compact geometry. Fin r+n ensures `f.Ordered C`. Slice as mixed product of actual master read amplitudes on input labels; axes NOT transformed. -/
variable {v:ℕ}
local notation "X"=> Cloud (Fin v)
local notation "Z"=> Cloud (Fin n)
local notation "Y"=> Cloud (Fin (v+n))
local notation "W"=> Wave (Fin v)
variable (p':Test (v+n))
noncomputable def uponL : X→L[ℝ] Points (v+n):= (Bay.phiL (v+n)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.pi (Fin.addCases (fun i=> ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Fin v=>E4) i) (fun _:Fin n=>0)))
abbrev laid (y:Cloud (Fin n)) : Points (v+n):= points (Fin.append 0 y)
abbrev lay {m n:ℕ}(x: Cloud (Fin m))(y:Cloud (Fin n)):=points (Fin.append x y)
lemma lain (x:Cloud (Fin v))(y:Cloud (Fin n)) : lay x y=laid y + (uponL (n:=n)) x :=by
   apply PiLp.ext; intro j; refine Fin.addCases (fun i=>?_) (fun i=>?_) j
   · unfold lay laid uponL; simp [phiL]
   unfold lay laid uponL; simp [phiL]
noncomputable def branch (z:Cloud (Fin n)):Wave (Fin v):= ⟨fun x=> p' (laid z+ (uponL (n:=n)) x),p'.contDiff.comp (contDiff_const.add ((uponL (n:=n) (v:=v)).contDiff))⟩
lemma bridged (x:Cloud (Fin v))(z:Cloud (Fin n)) : (branch p' z).val x=p' (lay x z):=by change p' _=_; rw [lain]
noncomputable def full (p':Test n):Complexion (Points n):=⟨p',p'.contDiff⟩
-- bound jointly through indicated high derivatives. On ANY physical spect placements (not even coarsely fixed).
lemma branched (k:ℕ) : ∃ B:ℝ,0≤B ∧ ∀ y:Cloud (Fin n),∀ x, ‖iteratedFDeriv ℝ k (branch p' y).val x‖≤B:=by
   obtain ⟨B,hB,hx⟩:=tall_any (u:=full p') (p'.hasCompactSupport) k; let L:= (@uponL v n) -- implicit order?
   refine ⟨B*‖(uponL (v:=v) (n:=n))‖^k,by positivity,fun y x=>?_⟩
   let L: X→L[ℝ] Points (v+n):=uponL; let f: Points (v+n)→ℂ:=fun x=>p' (laid y+x); have hψ: ContDiff ℝ ∞ f:= p'.contDiff.comp (contDiff_const.add contDiff_id)
   change ‖iteratedFDeriv ℝ k (f ∘ L) x‖≤ _; rw [L.iteratedFDeriv_comp_right (hψ) x (by exact_mod_cast le_top)]; apply le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..); simp only [Finset.prod_const,Finset.card_univ, Fintype.card_fin]; apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _); unfold f; rw [iteratedFDeriv_comp_add_left]; exact (hx k (le_refl _) (laid y + L x)).trans_eq (by simp)
lemma spanStays : ∃ B:ℝ,0≤B ∧ ∀ y:Cloud (Fin n), ∀ x∈Function.support (branch p' y).val, ‖x‖≤B:=by
   obtain ⟨a,ha⟩:= (p'.hasCompactSupport.image continuous_norm).bddAbove; refine ⟨|a|, by positivity, fun y x hx=> (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr ?_⟩; intro i; have ht:lay x y∈ tsupport p' := subset_closure (show p' (lay x y)≠0 by rw [← bridged]; exact hx); let P:= lay x y; rw [show x i=P (Fin.castAdd n i) from (Fin.append_left ..).symm]; apply (PiLp.norm_apply_le ..).trans ((ha ⟨_,ht,rfl⟩).trans (le_abs_self _))
-- moments sampled at BOTH y and x. Post fields C.seen actual in numerical. Cursor Φ returned after observational transformations.
variable (s:Fin v→ℕ) (F:(i:Fin v)→Leafage C (s i))(R:Fin n→ C.book.Token)
local notation "V"=> Fin v
local notation "U"=> Fin n
noncomputable def spect (R:Fin n→C.book.Token)(x:Fin n→Site (C.side N p))(v:Config G (C.side N p)):= ∏ i:Fin n,C.seen (R i) (x i) v
noncomputable def sees (p':Test (v+n))(x:Fin n→ Site (C.side N p)):=branch p' (C.S.place ∘ x)
include p' s R F in
noncomputable def jointS (m N p:ℕ):= (C.S.a N:ℂ)^(4*n)*∑ x:U→Site (C.side N p), moment (C.beta N p) (fun D=> multi C m N p s (fun i=> F i (N,p)) (sees p' (C:=C) (p:=p) (N:=N) x) D * spect R x D) -- dependent elaboration shadow N
local notation "I"=> Fin n→Site (C.side N p)
local notation "V'"=> Fin v→Site (C.side N p)
lemma cells (y:V')(x:I): Order.cells C N p (Fin.append y x)=lay (C.S.place ∘ y) (C.S.place ∘ x):=by apply PiLp.ext; intro j; refine Fin.addCases (fun i=>?_) (fun i=>?_) j<;> simp [Order.cells,lay]
lemma witness_column (P:Fin v → Trial C)(hP:∀ i:Fin v,∀ z: Site (C.side N p), Continuous (P i N p z)) : certificate (C:=C) (Fin.append P (fun i=> Bid.visits C (R i).1 (R i).2)) p' (N,p) = (C.S.a N:ℂ)^(4*n)*∑ x:I,moment (C.beta N p) (fun D=> sheet (sees p' (C:=C) (N:=N) (p:=p) x) C P N p D*spect (p:=p) (N:=N) R x D):=by
   let S:= Fin.append P (fun i=>Bid.visits C (R i).1 (R i).2); let u(x:I) := sees p' (C:=C) (p:=p) (N:=N) x; let t:ℂ:= C.S.a N
   have ht(y:V')(x:I): UVExt.Slots.probes N p (v+n) S (Fin.append y x)= moment (C.beta N p) (fun D=>(∏ i:V,P i N p (y i) D)*spect R x D):=by
       unfold UVExt.Slots.probes; congr 1; funext D; rw [Fin.prod_univ_add]; unfold S; simp_rw [Fin.append_left,Fin.append_right]; rfl
   unfold certificate; dsimp only; rw [show 4*(v+n)=4*n+4*v by omega,pow_add,mul_assoc,← Equiv.sum_comp (Fin.appendEquiv (α:=Site (C.side N p)) v n), Fintype.sum_prod_type]; apply congr_arg; rw [Finset.sum_comm,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
   let K (y:V'):= p' (Order.cells C N p (Fin.append y i)); let Wv(y:V')(D:Config G (C.side N p)):= (∏ j:V,P j N p (y j) D)*spect R i D
   have hW(y):Continuous (Wv y):= (continuous_finsetProd _ fun j _=>hP j _).mul (continuous_finsetProd _ fun _ _=> C.continuousO ..)
   have he(D): (∑ y:V',K y * Wv y D)* t^(4*v)= sheet (u i) C P N p D*spect R i D:=by
      unfold sheet; rw [Finset.prod_const, Finset.card_univ,Fintype.card_fin, ←pow_mul,mul_comm _ (t^_), mul_assoc, Finset.sum_mul]; apply congr_arg; refine Finset.sum_congr rfl (fun y _=>?_); unfold K; rw [cells]; unfold u sees; rw [bridged,mul_assoc];rfl
   change t^(4*v)*∑ y:V',K y * UVExt.Slots.probes N p (v+n) S (Fin.append y i)=_; simp_rw [ht]; unfold moment
   rw [show (fun D=> sheet (u i) C P N p D*spect R i D)=_ from funext (fun D=> (he D).symm),integral_mul_const,integral_finsetSum _ (fun y (_: y∈(Finset.univ:Finset V'))=>continuous_integrable _ ((hW y).const_mul _)),mul_comm]; simp_rw [integral_const_mul];rfl
end YM.RG05Readout.Chalice
