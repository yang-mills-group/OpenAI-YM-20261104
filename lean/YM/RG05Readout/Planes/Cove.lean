import YM.RG05Readout.Planes.Suites
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Planes
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
open Bay Chalice

/-!
# Cone receipts.Boolean Ward.
 Weighted REAL ancestry maps. Projection kernel not discarded here. This proves linear inverse attenuation for surviving low-engineering weights and propagation bound for the rest, not lower/separated aperture budget by assumption. Using m≫ as required from Husk.C. -/
local notation "Z!"=> C.path.levels
local notation "χ"=> Address.clear C
local notation "S"=> Palette C d
local notation "J"=> Mark C d
local notation "ξ"=> C.S.block
local notation "L"=> C.S.block i
local notation "p!"=> BudgetPoint
variable {e:ℕ}{s t α A E:ℝ}
local notation "ΠΩ"=> Address.clear C d e
local notation "T"=> LinearMap.id (R:=ℂ) (M:=S) - Address.clear C d e
local notation "Ω"=> amplify d C L
/-!
# Actual limiting dictionary including transitions on same extraction. E units threshold within. Holds in kernel identified by all Poem tests.This is same linear mapping in ANY extraction.H.Phase fields ported by common T.F. -/
open Function Filter MeasureTheory Extraction Next.Extract
open Petals Dash
variable {b₀:ℕ→ℕ} (Y:∀ d:ℕ,Cutoffs→ Emblems C d)
variable {T₀ S₀:YM.Table C.book}{L0:ℕ→YM.Table C.book}{W:DiffPlan T₀}{R:Dash.Bin S₀}(H:Next.Extract.Base C f S₀ L0 R T₀ W) {g:Extraction.Order}
variable {G':∀ d:ℕ,ℕ→Palette C d→ₗ[ℂ] C.label d}(hp:Chalice.Anchored D B h b₀ Y)(ht:Tune (dims:=b₀) H Y g G')
variable {q:Extraction.Order} {θ:∀ d:ℕ,Emblems C d}(hΘ:Tempo Y b₀ q θ)(hF:q.fuse ≤ (f.refine g).fuse)
/-! Pass plane camouflage to the actual continuum table T per extraction, even using a different DiffPlan (Final). Exact containment of the discounted incoming covers on each e-plane at this test convention.Requires ancestors bought from same C. -/
variable {Z₁:DiffPlan T₀}(he:e<d)(hM:b₀ d ≤ m)(T':Tint B C d m)
local notation "K₀"=> Cutoffs
-- nada
local notation "D'"=> fun a:Cutoffs=>Y d a
local notation "Z"=> G' d m
local notation "Tn"=> bounty B d
local notation "U!"=>C.S.a
variable {φ:Filter Cutoffs}[φ.NeBot] (hv:φ≤ q.fuse)(x:Cutoffs→Palette C d) {v:Palette C d}
include hp h H ht hM hF
variable {W' r'}(L':OPE.Package C W' r' D) (hA:Storage C D)(hG:G.Simple)(hBin:∀ d,UVExt.Slots.StrongBin C R f d)(hs:Z₁.Inclusions T₀)
include he hv hA hBin L' hs hG T'
local notation "o!"=> fun i:K₀=> ((↑(C.S.a i.1):ℂ)^(d-e))⁻¹

-- lift before cap any stencil.State.Regular
omit H ht hF hv hA L' hBin hs hG [φ.NeBot] in
private lemma stocked (hx:∃ c,∀ᶠ i in f.fuse,size (x i) ≤ c)(hk:∀ᶠ i in f.fuse, Address.clear C d e (fastU (Y d) x m i)=fastU (Y d) x m i): Slow C f (fun i:Cutoffs=> o! i • fastU (Y d) x m i):=by
   obtain ⟨c,hc⟩:=hx; let a:=C.S.a m; let t:= d-e; have hα:0<a:=C.S.a_pos _; let E₀:= c*((Tn m)*a^t)⁻¹
   have hr := charging (hp.age d)
   have hb:Slow C f (fun i:K₀=>Tn i.fst*E₀):=(show Slow C f (fun i:K₀=> Tn i.fst) from hr.comp (cutoff_grows f)).mul (Slow.const _)
   apply hb.reduce; filter_upwards [hc,hk,(cutoff_grows f).eventually_ge_atTop m] with i hu hp₁ hV
   obtain ⟨V,hW'⟩:= hp.paid i d (hM.trans hV); let v:= fastU (Y d) x m i; let b:= C.S.a i.1
   have hg : (finer (Y d i) hV).symm v=x i:= (congr_arg ((finer (Y d i) hV).symm ∘ id) (weave_fine hV ..)).trans (LinearEquiv.symm_apply_apply ..)
   have hs:(a/b)^t * ‖v‖ ≤ (Tn i.1/Tn m)*c:=
      (mul_le_mul_of_nonneg_left (size_norm v) (pow_nonneg (div_nonneg (C.S.a_pos _).le (C.S.a_pos _).le) _)).trans ((flare h (hp.age d) hW' T' hM (le_refl m) hV v he hp₁).2.trans (mul_le_mul_of_nonneg_left ((hg.symm ▸ size_cap e (x i)).trans (hg.symm ▸ hu)) (div_nonneg (zero_le_one.trans (bounty_head _)) (zero_le_one.trans (bounty_head _))))) -- adjust
   change ‖((b:ℂ)^t)⁻¹ • v‖≤ _; have hb:0<b:=C.S.a_pos _; rw [norm_smul,norm_inv,norm_pow,Complex.norm_real,Real.norm_of_nonneg hb.le]
   apply le_trans _ (Real.le_norm_self _);change _≤ Tn i.1 * E₀; unfold E₀; rw [div_pow,div_eq_mul_inv,mul_assoc] at hs; have ht:= mul_le_mul_of_nonneg_left hs (inv_pos.mpr (pow_pos hα t)).le; rw [inv_mul_cancel_left₀ (pow_pos hα t).ne'] at ht; exact ht.trans_eq (by rw [mul_inv_rev];ring)

lemma graded_in (hx:∃ c,∀ᶠ i in f.fuse,size (x i) ≤ c)(hk:∀ᶠ i in f.fuse, Address.clear C d e (fastU (Y d) x m i)=fastU (Y d) x m i)(hV:Tendsto x φ (𝓝 v)):
   T₀.project d (G' d m v) ∈ LinearMap.range (Z₁.rise he.le):=by
      have hg:=hv.trans hF; let z:=Z v; have hx':= Tune.projection h x H hBin L' hA hG Y (Anchored.tracks h b₀ Y hp) ht hM hg hV hx
      have hf:=stocked h Y hp he hM T' x hx hk
      obtain ⟨j,p,Q,h',hP⟩:=forums H e; obtain ⟨k,hL,hk'⟩:= ((eventually_all.mpr (fun i:Fin p=>eventually_ge_atTop (craving (Q i) d))).and hx'.2).exists
      obtain ⟨x',hx',hX⟩:=hk'; let As:= Petals.code m k (fastU (Y d) x m)
      obtain ⟨a,hc⟩:= favored h (Y d) x (Anchored.tracks h b₀ Y hp d) hM _ hx.choose_spec L' hA hG H (hBin _) hP he.le hf hL
      have he':φ ≤ f.fuse:= hg.trans (Tails.refine f g).fused
      obtain ⟨ℓ,hℓ,hl,a',ha⟩:= Next.UVStress.finite_extract a (hc.2.2.1.choose) (Eventually.filter_mono he' ((Order.fused f (fun i=> ‖a i‖≤_)).mpr hc.2.2.1.choose_spec)) -- parentheses
      -- now both S projections compare. Need exactly in all spectra against ordinary T:
      refine ⟨T₀.project e a', T₀.field_ext H.kernel.laws.toSymmetric ?_⟩; intro n w s hu
      rw [hs.kernels _ _ hu]; simp_rw [MonitorOps.head T₀ H.kernel.laws.toSymmetric _ w hu]; let W' : Fin n → C.book.Token :=fun i=> ⟨(w i).1,T₀.representative _ (w i).2⟩
      let f'(v:C.book.Token)(s:Points (n+1)):=T₀.read s (Fin.cons v W')
      apply (Test.unique_kernel (K:=f' ⟨e,a'⟩) (P:=f' ⟨d,z⟩) (T₀.smooth_read H.kernel.smooth _|>.continuousOn) (T₀.smooth_read H.kernel.smooth _|>.continuousOn)).1 ?_ hu; intro t
      let v:= Shot.mk _ 0 (Fin.cons (α:=fun _ => C.book.Token) ⟨d,z⟩ W') t
      have hel:= tendsto_nhds_unique (Petals.forecast h H (hℓ.trans he') hc ha v) (Petals.forecast h H (hℓ.trans he') hx' (hX.mono_left hℓ) v)
      have he(z:C.book.Token) : Function.update (v.left) 0 z= Fin.cons z W':=by unfold v; simp
      change t.applyTo (fun x=>T₀.read x (Function.update v.left 0 (⟨e,a'⟩:C.book.Token)))= t.applyTo (fun x=>T₀.read x (Function.update v.left 0 (⟨d,z⟩:C.book.Token))) at hel
      rw [he,he] at hel; exact hel
end YM.RG05Readout.Planes
