import YM.RG05Readout.Velvet.Stripe
import YM.RG05Readout.Bay.Audible
import YM.OPE.Exchange.Regime
/-! Actual detector volume telescope. Key nonvanishing separation
 at WM collars. Hull.Pos documented.Plane calibration.Reader resampling at
 A step with torus inside ancestry only. This works at all physical offsets. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Velvet
open Function MeasureTheory Set Filter Topology Pulse Native Address Many Lattice Wilson Extraction WithLp Nuclear Bay
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{m n j:ℕ}{q R η ζ:ℝ}
structure Sky (Ψ:Wave (Fin m)) (R η:ℝ) : Prop where
    pos:0<η
    caps :0≤ R
    shape: ∀ x∈ tsupport Ψ.val,∀ i:Fin m,‖x i‖≤R
    spread : Scattering Ψ η
variable {Ψ:Wave (Fin m)} (hp:Sky Ψ R η)
lemma Sky.park (hp:Sky Ψ R η) : IsCompact (tsupport Ψ.val):= (isCompact_closedBall (0:Cloud (Fin m)) R).of_isClosed_subset (isClosed_tsupport _) (fun x hx=> Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact (pi_norm_le_iff_of_nonneg hp.caps).mpr (hp.shape x hx)))
open Metric Poem
lemma grid_spaced {x y:Cover} (he:x≠y) : C.S.a j≤ dist (C.S.gridPoint j x) (C.S.gridPoint j y):=by
    obtain ⟨i,hi⟩:= Function.ne_iff.mp he -- check
    let a:= C.S.a j; have ha:0 ≤ a:=C.S.a_pos _|>.le
    have hv: ‖(C.S.gridPoint j x - C.S.gridPoint j y) i‖= a*|(x i - y i:ℤ)|:=by rw [PiLp.sub_apply]; change ‖a*(x i:ℝ)-a*(y i:ℝ)‖=_;rw [← mul_sub,norm_mul,Real.norm_of_nonneg ha,Real.norm_eq_abs]; push_cast;rfl
    rw [dist_eq_norm]; apply le_trans _ (PiLp.norm_apply_le _ i); rw [hv]; apply le_mul_of_one_le_right ha; exact_mod_cast (show 1 ≤ |x i-y i| from abs_pos.mpr (sub_ne_zero.mpr hi))
variable (D:Poem C j)
local notation "I"=> Fin D.n
local notation "s"=> (C.S.a j)
local notation "g"=> D.opening
local notation "X"=> Points D.n
local notation "V"=> Points m
local notation "T"=> D.template
local notation "W"=> Lattice.wrap
local notation "L"=> tsupport D.opening.val
lemma boxC : IsCompact L:= (isCompact_closedBall (0:E4) _).of_isClosed_subset (isClosed_tsupport _) D.opening_there
lemma template_center : T 0=0:=by unfold template; simp [D.centered,OPE.grid_zero]
def rim (D:Poem C j) : Set (Points D.n):= (bag D.n)⁻¹' (Set.univ.pi (fun i=>tsupport (D.post i).val))
local notation "P"=> rim D
lemma rimSmall : IsCompact (rim D):= (bag _).toHomeomorph.isCompact_preimage.mpr (isCompact_univ_pi (fun i=> (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure (D.tucked i)))
def pluck (D:Poem C j)(x:Points D.n):ℂ:= ∏ i:Fin D.n,(D.post i).val (x i)
lemma pluckSmooth : ContDiff ℝ ∞ (pluck D):= contDiff_prod (f:=fun i (x:Points D.n)=>(D.post i).val (x i)) (fun i _=> (show ContDiff ℝ ∞ (D.post i).val from (D.post i).property).comp ((contDiff_apply ℝ _ i).comp (f:=bag _) (bag D.n).contDiff))
lemma pluck_mem : tsupport (pluck D) ⊆ P:= by
    apply closure_minimal _ (rimSmall D).isClosed; intro x hx; apply Set.mem_univ_pi.mpr; intro i; exact subset_closure (fun h=> hx (Finset.prod_eq_zero (Finset.mem_univ i) h))
lemma spanned {y:X} (hx:y∈P) (i:I) : dist (y i) (D.template i.succ) ≤ s/16:=mem_closedBall.mp (D.tucked i (Set.mem_univ_pi.mp hx i))
open OPE
lemma sentries {z:E4}{y:Points D.n}(hz:z∈ L)(hy:y∈ P) : ClearOf z y.ofLp (s/2):=by
   have he(i k:Fin (D.n+1))(ht:i ≠ k): s ≤ dist (D.template i) (D.template k):= grid_spaced (D.key_one.ne ht); have ha:s>0:=C.S.a_pos _
   constructor
   · intro i; rw [← dist_eq_norm]; have hw:= dist_triangle4 (T 0) z (y i) (T i.succ) -- check
     have ht:= he 0 i.succ (Fin.succ_ne_zero i|>.symm); have hH:=spanned D hy i; have hx:dist (T 0) z ≤ s/16:=by rw [template_center,dist_comm]; exact mem_closedBall.mp (D.opening_there hz)
     change _ ≤ dist z (y i); linarith
   intro i k ht; rw [← dist_eq_norm]; change _≤ dist (y i) (y k); have hw:= dist_triangle4 (T i.succ) (y i) (y k) (T k.succ); rw [dist_comm (T i.succ) (y i)] at hw; linarith only [he _ _ (Fin.succ_injective D.n|>.ne ht),hw,spanned D hy i,spanned D hy k,ha]
include hp
lemma inner_fit (z:E4){x:V}(hx:x∈ scoreHull Ψ)(he:0<q) : WithinRoom q R η (WithLp.ofLp (beginAt q z x)) z:=by
    constructor
    · intro i; change ‖beginAt q z x i-z‖≤_; rw [short,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg he.le, mul_comm R _]; exact mul_le_mul_of_nonneg_left (hp.shape _ hx _) he.le
    intro i k h; change η*q≤ ‖beginAt _ z x _-beginAt _ z x _‖; rw [short,short,add_sub_add_left_eq_sub, ←smul_sub,norm_smul, Real.norm_of_nonneg he.le,mul_comm]; exact mul_le_mul_of_nonneg_left (hp.spread _ hx i k h) he.le -- implicit η notation
variable (he:0<q)(hQ: R*q< C.S.a j/2)
include he hQ
lemma enclave {x: Points m}{y:Points D.n}(hp':x∈ pad Ψ g q)(hr:y∈ P) : ribbon x y∈ conf (m+D.n):=by
   obtain ⟨⟨z,x⟩,⟨hz,hH⟩,rfl⟩:=hp'; let x':=beginAt q z x; have hk:= inner_fit (q:=q) hp z hH he; have hf:= sentries D hz hr; change Injective (Fin.append (WithLp.ofLp (x')) y.ofLp)
   have ha:s>0:=C.S.a_pos _; have hη:0<η:=hp.pos
   have hy(i:Fin m)(k:Fin D.n):x'.ofLp i ≠ y.ofLp k:=by intro hl; have h:=hk.span i; have ht:=hf.openSpace k; rw [←hl,norm_sub_rev] at ht; exact lt_irrefl _ ((h.trans_lt hQ).trans_le ht)
   intro i j h; revert h; refine Fin.addCases (fun i=> ?_) (fun i=> ?_) i <;> refine Fin.addCases (fun j=>?_) (fun j=>?_) j <;> intro h
   · simp only [Fin.append_left] at h; apply congr_arg; by_contra hx; have hz:= hk.spaced _ _ hx; exact (mul_pos hη he|>.not_ge) (by rw [h,sub_self,norm_zero] at hz; exact hz)
   · exact (hy i j (by simpa using h)).elim
   · exact (hy j i (by simpa using h.symm)).elim
   apply congr_arg; by_contra hz; have hv:=hf.spread _ _ hz; simp only [Fin.append_right] at h; rw [h,sub_self,norm_zero] at hv; linarith only [hv,ha]
-- aligned blurb identity
local notation "p'"=> pluck D
noncomputable def blurb (D:Poem C j) (Ψ:Wave (Fin m))(q:ℝ) : Points m × Points D.n→ℂ:= fun z=> pattern (molten Ψ q (boxC D)) z.1 * pluck D z.2
omit hQ in
lemma blurb_stock : tsupport (blurb D Ψ q)⊆ pad Ψ g q ×ˢ P :=by
    apply closure_minimal _ ((padSmall (q:=q) (boxC D) hp.park).prod (rimSmall D)).isClosed; intro x hx; exact ⟨outline _ hp.park he (subset_closure (left_ne_zero_of_mul hx)),pluck_mem D (subset_closure (right_ne_zero_of_mul hx))⟩
-- Def.Read
noncomputable def telegram (hp:Sky Ψ R η)(he:0<q)(hQ:R*q<C.S.a j/2) : Test (m+D.n):=by
   let e:=stripe m D.n; let v:=blurb D Ψ q; have hv : tsupport (v∘e) ⊆ e⁻¹' (pad Ψ g q ×ˢ P):= (tsupport_comp_subset_preimage _ e.continuous).trans (Set.preimage_mono (blurb_stock hp D he)) -- order
   refine ⟨v ∘ e,?_, (e.toHomeomorph.isCompact_preimage.mpr ((padSmall (boxC D) hp.park).prod (rimSmall D))).of_isClosed_subset isClosed_closure hv, fun x hx=>?_⟩
   · let f:= (molten Ψ q (boxC D)); apply ContDiff.comp (f:=e) _ e.contDiff; exact (((show ContDiff ℝ ∞ f.val from f.property).comp (f:=bag _) (bag m).contDiff).comp contDiff_fst).mul ((pluckSmooth D).comp contDiff_snd)
   have ht:= hv hx; have hw:x = ribbon (e x).1 (e x).2:= (e.symm_apply_apply x).symm; rw [hw]; exact enclave hp D he hQ ht.1 ht.2
lemma telegram_read (x:Points m)(y:Points D.n): telegram D hp he hQ (ribbon x y)=blurb D Ψ q (x,y):=by
    let e:=stripe m D.n; change blurb D Ψ q (e (e.symm (x,y)))=_; rw [ContinuousLinearEquiv.apply_symm_apply]
end YM.RG05Readout.Velvet
