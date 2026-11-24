import YM.FormalBulk08.Flat.Pairs

/-!
# Estimates with (disposable) fixed powers of inverse coarse momentum

Serving A0/T on existing Towers conventions. Both costs here are post-block
(not the final strip width!). No unspecified J- or L-dependent *exponent*
of coarse momentum or UV depth.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Flat
open Filter Set Function Lattice Laurent Bloch Exterior Precision RG Next.Free UVExtension.Free
open scoped Topology BigOperators
variable {G : Gauge} {ι : Type*} {t j : ℕ}

/-- Freeze Patch and L while comparing two towers. -/
structure Gate (j t : ℕ) where
  sample : Flight j t
namespace Gate
variable (q : Gate j t)

abbrev ride (V : Train j) : Flight j t := { q.sample with wing := V }
abbrev L := q.sample.L

lemma table_floor (k : ℝ) (hk : 0<k) : ∃ c : ℝ, 0<c ∧ ∀ V p, p∈baseCube → p≠0 → c ≤ ‖(q.ride V).tabE k p‖ := by
  obtain ⟨b,C,hb,h⟩:=levelD_caps j q.sample.legal k hk
  let L:= q.L
  let m:=L.val
  let U:= ‖((m:ℂ)^2)⁻¹‖; have hU : 0<U := norm_pos_iff.mpr (inv_ne_zero (pow_ne_zero _ (side_ne L)))
  let a := Real.exp (-(4*plankCost)); let v:=a^j
  have hv : 0<v := pow_pos (Real.exp_pos _) _
  refine ⟨(v*v)*(U*b),mul_pos (mul_pos hv hv) (mul_pos hU hb),fun V p hp he=> ?_⟩
  let y (l : Site q.L) := yen (massFilter q.sample.patch) (aliasAt p l)
  let d (l : Site q.L) (i : Axis) := scaleD q.L k V (aliasAt p l) i
  let g l := y l*∑ i,d l i
  have ht l : Silver (y l) := q.sample.filter_silver (alias_real hp.1 l)
  have hd l i : Silver (d l i) := ((Silver.side _).pow _).inv.mul (Train.D_cost _ hk _ _ (alias_real hp.1 _))
  have h₁ l : Silver (g l) := (ht l).mul (Silver.sum _ _ (fun i _=>hd l i))
  have hE (p : Momentum) (hp : p ∈ realCube zone) : v ≤ ‖massFilter q.sample.patch (narrow L p)‖ := by
    have he := Train.area_at_root L L le_rfl p hp
    rw [div_self (side_pos L).ne',mul_one] at he
    unfold massFilter; rw [norm_pow]; exact pow_le_pow_left₀ (Real.exp_pos _).le he _
  have hm := base_subset_realCube zone_pos hp
  have hY : v*v ≤ (y 0).re := by
    rw [← (ht 0).norm]
    unfold y yen; rw [alias_zero_eq, norm_mul, ← narrow_neg]; exact mul_le_mul (hE _ hm) (hE _ (realCube_neg hm)) hv.le (norm_nonneg _)
  have hP : U*b ≤ (d 0 0).re := by
    rw [← (hd 0 0).norm]
    unfold d scaleD; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (h V _ _ (alias_base hp _ q.sample.odd) (alias_regular (P:=q.sample) hm (0:Site q.L) (Or.inr he)).2).1 hU.le
  apply le_trans _ (Complex.re_le_norm (∑ l,g l)); rw [Complex.re_sum]
  refine le_trans ?_ (Finset.single_le_sum (f:=fun l => (g l).re) (fun i _=> (h₁ i).re_nonneg) (Finset.mem_univ 0))
  unfold g; rw [(ht 0).real_mul, Complex.re_sum]
  exact mul_le_mul hY (hP.trans (Finset.single_le_sum (f:=fun i=> (d 0 i).re) (fun i _=> (hd 0 i).re_nonneg) (Finset.mem_univ 0))) (mul_pos hU hb).le ((ht _).re_nonneg)
end Gate

variable {p : ι→Momentum} {w r : ι→ℝ} (hx : Range p w)

lemma signal_cont (S : Side) (n : ℕ) (i m) : Continuous fun p => signal S n p i m := by
  simp only [signal,wedge,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,tripQ,chip]; fun_prop
include hx in
lemma signal_paired (S : Side) (n : ℕ) (hr : ∀ i,0 ≤ r i) :
    Boards w r 0 (fun i=>signal S n (p i)) fun i=>signal S n (p i) := fun i m => hx.on_axis hr _ (signal_cont S n i m)
include hx in
lemma mirage_paired (S : Side) (n : ℕ) (hr : ∀ i,0≤r i) :
    Boards w r 0 (fun i=>mirage S n (p i)) fun i=>mirage S n (p i) := fun i m=> hx.on_axis hr (fun p=> signal S n (-p) m i) ((signal_cont S n m i).comp continuous_neg)
lemma filter_cont (P : Patch) : Continuous (massFilter P) := by unfold massFilter area plank rail twirl; fun_prop
include hx in
lemma flux_same (q : Flight j t) (n : ℕ) (hr : ∀ i,0≤r i) : Boards w r 0 (fun i=>flux q n (p i)) fun i=>flux q n (p i) := by
  intro i m; refine hx.on_axis hr (fun p=>flux q n p i m) ?_
  by_cases h : m=i
  · subst m; simp only [flux,hinges,mask,Matrix.transpose_apply,Matrix.smul_apply,Matrix.diagonal_apply_eq]
    apply Continuous.smul ((filter_cont _).comp continuous_neg); unfold inventory rail twirl; fun_prop
  simp only [flux,hinges,mask,Matrix.transpose_apply,Matrix.smul_apply,Matrix.diagonal_apply_ne _ h,smul_zero]
  exact continuous_const

namespace Probe
variable {V W : ι→Train j} {A : ι→Levels G} {i N N' : ι→ℕ}
variable (h : Probe V W A i N N') (hr : ∀ x,fineR (A x) (N x) (i x) ≤ r x)
variable (hj : 4≤j) (k : ℝ) (hk : 0<k)
include hx h hr hj hk
lemma field (S : Side) : Boards w r 2 (fun x=>fieldD S k (V x) (p x)) fun x=>fieldD S k (W x) (p x) := by
  have he x := (fineR_pos ..).le.trans (hr x)
  exact Boards.mask_paired (fun x=>scaleD S k (V x) (p x)) (fun x=> scaleD S k (W x) (p x)) (n:=1) hx.atLeast he
    (fun a=> (Paired.const (((S.val:ℂ)^2)⁻¹) he).mul (basic h hj hx hr k hk a))
lemma bound_pipe : Boards w r 12 (fun x=> pipe 1 k (V x) (p x)) fun x=> pipe 1 k (W x) (p x) := by
  have he x := (fineR_pos ..).le.trans (hr x)
  have hh : Boards w r 2 (fun x=> fieldI 1 k (V x) (p x)) fun x=> fieldI 1 k (W x) (p x) := by
    simp only [fieldI,scaleD_one]
    exact Boards.mask_paired _ _ (n:=1) hx.atLeast he (backwards h hj hx hr k hk)
  have hy : ∀ (x : Train j) p, scaleR 1 k x p=Train.rho k x p := fun x p=> by simp [scaleR]
  simp only [pipe,hy]
  exact Boards.sm (quota_back h hj hx hr k hk) (Boards.times hx.atLeast he (mirage_paired hx 1 0 he) hh)
lemma bound_rotor : Boards w r 14 (fun x=> rotor 1 k (V x) (p x)) fun x=> rotor 1 k (W x) (p x) := by
  have he x := (fineR_pos ..).le.trans (hr x)
  exact Boards.times hx.atLeast he (Boards.times hx.atLeast he (mirage_paired hx 1 1 he) (pink_tabs h hj hx hr k hk)) (signal_paired hx 1 1 he)
end Probe
namespace Gate
variable {V W : ι→Train j} {A : ι→Levels G} {i u N N' : ι→ℕ}
variable (q : Gate j t) (h : Probe V W A i N N') (hr : ∀ x,fineR (A x) (N x) (i x) ≤ r x)
variable (k : ℝ) (hk : 0<k)
include h hr hk hx
lemma table_tabs : Paired w r 2 (fun x=> (q.ride (V x)).tabE k (p x)) fun x=> (q.ride (W x)).tabE k (p x) := by
  have he x := (fineR_pos ..).le.trans (hr x)
  let D (l : Site q.L) (F : ι→Train j) (x):= yen (massFilter q.sample.patch) (aliasAt (p x) l) *
    ∑ a, scaleD q.L k (F x) (aliasAt (p x) l) a
  refine Paired.sum (Finset.univ (α:=Site q.L)) hx.atLeast he (fun i=> D i V) (fun i=>D i W) fun a _=> ?_
  let g x := aliasAt (p x) a; have hu := hx.images q.L q.sample.odd a
  let Y := massFilter q.sample.patch
  have hh : Continuous (yen Y) := Continuous.mul (filter_cont _) ((filter_cont _).comp continuous_neg)
  apply (hu.on_axis he _ hh).mul (t:=0) (s:=2)
    (Paired.sum Finset.univ hx.atLeast he (fun i x=>scaleD q.L k (V x) (g x) i) (fun i x=>scaleD q.L k (W x) (g x) i) ?_)
  exact fun a _=> (Paired.const (((q.L.val:ℂ)^2)⁻¹) he).mul (Probe.basic h q.sample.legal hu hr k hk a)

lemma weights_tabs (l : Site q.L) :
    Paired w r 4 (fun x=> (q.ride (V x)).weightsE k (p x) (aliasAt (p x) l))
      fun x=> (q.ride (W x)).weightsE k (p x) (aliasAt (p x) l) := by
  have he x := (fineR_pos ..).le.trans (hr x)
  obtain ⟨c,hc,hh⟩:=q.table_floor k hk
  have hh := (table_tabs hx q h hr k hk).recip (s:=0) hx.atLeast he ⟨c,hc,fun i=> by
    rw [pow_zero,div_one]; exact ⟨hh _ _ (hx.cube i) (hx.away i),hh _ _ (hx.cube i) (hx.away i)⟩⟩
  have ht := hx.images q.L q.sample.odd l
  let g x:=aliasAt (p x) l
  have hT := ht.on_axis he _ ((filter_cont q.sample.patch).comp continuous_neg)
  have ha : Paired w r 2 (fun x=>(q.ride (V x)).total k (g x)) fun x=> (q.ride (W x)).total k (g x) :=
    Paired.sum Finset.univ hx.atLeast he (fun i x=>scaleD q.L k (V x) (g x) i) (fun i x=> scaleD q.L k (W x) (g x) i)
      (fun a _=> (Paired.const (((q.L.val:ℂ)^2)⁻¹) he).mul (Probe.basic h q.sample.legal ht hr k hk a))
  simp only [Flight.weightsE, div_eq_mul_inv]
  exact (hT.mul ha).mul hh

variable (ht : 4≤t) (hc : Probe (fun x=> (q.ride (V x)).land) (fun x=> (q.ride (W x)).land) A u N N')
    (hs : ∀ x,fineR (A x) (N x) (u x)≤r x)
include ht hc hs
lemma pilot_tabs (l : Site q.L) : Boards w r 16 (fun x=> (q.ride (V x)).pilot k (p x) l)
    fun x=> (q.ride (W x)).pilot k (p x) l := by
  have he x := (fineR_pos ..).le.trans (hr x)
  have hh := hx.images q.L q.sample.odd l
  have h₁ := Boards.times hx.atLeast he (Boards.times hx.atLeast he (Probe.field hh h hr q.sample.legal k hk q.L)
    (flux_same hh q.sample 1 he)) (Probe.bound_rotor hx hc hs ht k hk)
  have h₂ := Boards.sm (weights_tabs hx q h hr k hk l) (Boards.times hx.atLeast he (signal_paired hh q.L 0 he)
    (Probe.bound_pipe hx hc hs ht k hk))
  exact (h₁.add h₂).plugs (fun x=> (Flight.pilot_match k hk (q.ride (V x)) (base_subset_realCube zone_pos (hx.cube x)) (hx.away x) l).symm)
    (fun x=> (Flight.pilot_match k hk (q.ride (W x)) (base_subset_realCube zone_pos (hx.cube x)) (hx.away x) l).symm)
lemma wire_tabs (l : Site q.L) : Boards w r 28 (fun x=> (q.ride (V x)).wire k (p x) l)
    fun x=> (q.ride (W x)).wire k (p x) l := by
  have he x := (fineR_pos ..).le.trans (hr x)
  have hL:= hx.atLeast
  have hh := hx.images q.L q.sample.odd l
  let g x:=aliasAt (p x) l
  have h₁ := Boards.times hL he (Boards.times hL he (Boards.times hL he (Boards.times hL he
    (Probe.pink_tabs h q.sample.legal hh hr k hk) (signal_paired hh q.L 1 he))
    (Probe.field hh h hr q.sample.legal k hk q.L)) (flux_same hh q.sample 1 he)) (mirage_paired hx 1 1 he)
  have ha : Paired w r 12 (fun x=> (q.ride (V x)).chainY k (p x) (g x)) fun x=> (q.ride (W x)).chainY k (p x) (g x) := by
    have hg : Continuous (yen (massFilter q.sample.patch)) := Continuous.mul (filter_cont _) ((filter_cont _).comp continuous_neg)
    have hv := (hh.on_axis he _ hg).mul ((Paired.const (((1:Side).val:ℂ)^4) he).mul (Probe.quota hc ht hx hs k hk))
    have hy := (Probe.quota_back h q.sample.legal hh hr k hk).mul (Paired.const (((q.L.val:ℂ)^4)⁻¹) he)
    simp only [Flight.chainY, scaleR,div_eq_mul_inv, _root_.mul_inv_rev]; exact hv.mul hy
  have hq : Boards w r 16 (fun x=> (q.ride (V x)).cloud k (p x)) fun x=> (q.ride (W x)).cloud k (p x) :=
    Boards.times hL he (Boards.times hL he (Boards.times hL he (Probe.pink_tabs hc ht hx hs k hk)
      (signal_paired hx 1 1 he)) (Probe.field hx hc hs ht k hk 1)) (mirage_paired hx 1 1 he)
  have h₂ := Boards.sm ha (Boards.times hL he (flux_same hh q.sample 2 he) (((Boards.fixed (w:=w) he (1 : Frequency 2 2)).extra hL he (Nat.zero_le 16)).sub hq))
  exact ((h₁.extra hL he (show _ ≤ 28 by decide)).add h₂).plugs (fun x=> (Flight.wire_match k hk (q.ride (V x)) (base_subset_realCube zone_pos (hx.cube x)) (hx.away x) l).symm)
    (fun x=> (Flight.wire_match k hk (q.ride (W x)) (base_subset_realCube zone_pos (hx.cube x)) (hx.away x) l).symm)
end Gate
end YM.FormalBulk08.Flat
