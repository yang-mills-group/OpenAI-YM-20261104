import YM.RG05Readout.Planes.Coupon
import YM.OPE.Orbits.System
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
variable {Z₁:DiffPlan T₀}(hM:b₀ d ≤ m)(T':Tint B C d m)
local notation "K₀"=> Cutoffs
-- nada
local notation "Z"=> G' d m
local notation "Tn"=> bounty B d
local notation "U!"=>C.S.a
variable {φ:Filter Cutoffs}[φ.NeBot] (hv:φ≤ q.fuse)(x:Cutoffs→Palette C d) {v:Palette C d}
variable {W' r'}(L':OPE.Package C W' r' D) (hA:Storage C D)(hG:G.Simple)(hBin:∀ d,UVExt.Slots.StrongBin C R f d)(hs:Z₁.Inclusions T₀)
local notation "o!"=> fun i:K₀=> ((↑(C.S.a i.1):ℂ)^(d-e))⁻¹
open OPE Orbits

/-!
# qru in each contract. Use unselected/covariant actual Reader on SAME Final. Basis.Sign.MReceipt.Tiling carries. Numbers assembled actual references, inverse used later. -/
-- b base reference fixed.Coupling-s differences.Shells.Fram
local notation "M'"=> fun i:ℕ=> powerFare B d i
noncomputable abbrev cuts (T₀:YM.Table C.book)(G':∀ d:ℕ,ℕ→ Palette C d→ₗ[ℂ] C.label d) (d m:ℕ) : Palette C d →ₗ[ℂ] T₀.Field d:= (T₀.project d).comp (G' d m)
local notation "K'"=> cuts T₀ G'
local notation "κ"=> quotaP C B d
include ht hp h hM H hΘ hF
variable {V:Type*}[NormedAddCommGroup V][NormedSpace ℂ V](F:T₀.Field d→L[ℂ]V)
include T' L' hA hBin hs hG
lemma contract_toll (he:e ≤ d)(x:Palette C d)(hi:m≤ i)(hx:∀ i:ℕ,∀ hp:i<e,∀ x:T₀.Field i,F (Z₁.rise (hp.le.trans he) x)=0):
    let P:= F.comp ((K' d m).toContinuousLinearMap)
    ‖F (cuts T₀ G' d i x)‖≤ (U! i/U! m)^d * ‖P‖ * quotaP C B d (d-e) m i *size x:=by
     intro P; let D':=quotaP C B d (d-e) m i; let a:=lightest C d m i; let Sx:=finer (θ d) hi; have ht' : F (cuts T₀ G' d i x)= a • P (Sx.symm x):=by
        rw [show cuts T₀ G' d i x=_ from tune_level Y H ht hΘ hF hi hM x]; change F ((K' d m) (a • _))=_;rw [map_smul,map_smul];rfl
     have hz:0<U! i/U! m:=div_pos (C.S.a_pos _) (C.S.a_pos _);rw [ht',norm_smul,show ‖a‖= _ from (show ‖a‖=(U! i/U! m)^d from (by unfold a lightest; rw [norm_pow, norm_div, Complex.norm_real,Complex.norm_real, Real.norm_of_nonneg (C.S.a_pos _).le, Real.norm_of_nonneg (C.S.a_pos _).le]))]; change (U! i/U! m)^d* _ ≤ _ * D'* _; rw [mul_assoc,mul_assoc]; apply mul_le_mul_of_nonneg_left _ (pow_pos hz _|>.le); -- goal RHS perhaps ‖P‖*(D...)
     by_cases hm:e=0
     · have hf:= origin0 h Y hp hΘ hM (d:=d) x hi;
       calc ‖P (Sx.symm x)‖ ≤ _:= P.le_opNorm _
            _ ≤ _:= le_trans (mul_le_mul_of_nonneg_left hf (norm_nonneg _)) (le_of_eq (by simp only [D',hm,Nat.sub_zero]))
     obtain ⟨w,⟨u,hw⟩,hb⟩:= epilogue (e:=e-1) h Y H hp ht hΘ hF (show e-1 < d by omega) hM T' L' hA hG hBin hs x hi
     rw [show e-1+1=e by omega] at hb
     have ht:F (cuts T₀ G' d m w)=0:=by change F (T₀.project _ (G' d m w))=_; rw [← hw]; exact hx _ (by omega) u
     rw [← show P (Sx.symm x-w)=_ from (show P (Sx.symm x-w)=P (Sx.symm x) by rw [map_sub,show P w=0 from ht,sub_zero])]; exact (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))

omit ht hM H hΘ hF L' hA hBin hs hG T' in
lemma fare_lives (e:ℕ) (m:ℕ) : RateLE atTop C.S.scale (quotaP C B d e m) (e:ℝ):=by
   let q(i):=1+grow (powerFare B d i); have ht:= C.S.divergent; have he:RateLE atTop C.S.scale q 0:= RateLE.of_norm_le (charging' (hp.age d)) (Eventually.of_forall (fun i=>by unfold q; rw [Real.norm_of_nonneg (add_nonneg zero_le_one (zero_le_one.trans (grows _).2.1))]; exact le_mul_of_one_le_left (add_nonneg zero_le_one (zero_le_one.trans (grows _|>.2.1))) (grows _|>.1)))
   let t := fun i:ℕ=> (C.S.a m/C.S.a i)^e; have hw: RateLE atTop C.S.scale t (e:ℝ) :=by
      have H: Height C.S atTop C.S.scale id 1:= level_height tendsto_id; simpa only [t,id_eq,zero_sub,neg_neg,mul_one] using (((RateIs.const ht (C.S.a_pos m)).div H.mesh).power e).pays ht
   have hp:= ((charging (hp.age d)).mul hw).mul he; rw [zero_add,add_zero] at hp; exact hp
omit hM T'
lemma tight_plane (he:e ≤ d)(hx:∀ i:ℕ,∀ hp:i<e,∀ x:T₀.Field i,F (Z₁.rise (hp.le.trans he) x)=0): RateLE atTop C.S.scale (fun m:ℕ=> F.comp ((cuts T₀ G' d m).toContinuousLinearMap)) (-(e:ℝ)) :=by
    have he':= service_fine (hp.age d); obtain ⟨m₀,hm₀⟩:=eventually_atTop.mp (he'.and (eventually_ge_atTop (b₀ d))); have hM:Tint B C d m₀:= ⟨fun i hi=> (hm₀ i hi).1⟩; have hk:= (hm₀ m₀ le_rfl).2
    let κ₀:= F.comp (K' d m₀|>.toContinuousLinearMap); let c : ℝ:= Fintype.card (Mark C d); let z(i):=(U! i/U! m₀)^d * ‖κ₀‖ * quotaP C B d (d-e) m₀ i * c
    have hz:RateLE atTop C.S.scale z (-(e:ℝ)):=by
       have H:Height C.S atTop C.S.scale id 1:=level_height tendsto_id; have h:=C.S.divergent
       have hu:= (((((H.mesh.div (RateIs.const h (C.S.a_pos m₀))).power d).pays h).mul (RateLE.const ‖κ₀‖ h)).mul (fare_lives (d:=d) (by exact ‹C.Makes›) Y hp (d-e) m₀)).mul (RateLE.const c h); simp only [Nat.cast_sub he] at hu; exact ((hu.mono (b:=-(e:ℝ)) (by linarith only))).congr (Eventually.of_forall fun i=>rfl)
    apply RateLE.transfer hz; filter_upwards [eventually_ge_atTop m₀] with i hi; refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (z i)) (fun x=> ?_); let w₁:=K' d i x; refine (contract_toll h Y H hp ht hΘ hF hk hM L' hA hG hBin hs F he x hi hx).trans ?_; -- argument order
    unfold z; refine (mul_le_mul_of_nonneg_left (size_paid x) ?_).trans (by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (Real.le_norm_self _) (norm_nonneg _));
    unfold quotaP; have ht:=bounty_head (d:=d) (B:=B) i; have he:=grows (d:=d) (B:=B) i |>.2.1; have h':0< U! i:=C.S.a_pos _; have hv:=C.S.a_pos m₀; positivity

-- consume FINAL covariant cuts immediately
variable {U:Spec.Final C f T₀}(U':Orbits.Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
omit hs
include U'
lemma tally (e d:ℕ)(he:e≤ d) : RateLE atTop C.S.scale (fun m:ℕ=> (LinearMap.toContinuousLinearMap (U'.cutTest e d)).comp ((cuts T₀ G' d m).toContinuousLinearMap)) (-(e:ℝ)):=
    tight_plane h Y H hp ht hΘ hF L' hA hG hBin U'.lifts _ he (fun i hb x=>by change U'.cutTest e d ((Spec.Final.sector U).derivatives.rise _ x)=_; rw [U'.cut_rise]; exact U'.kills_lower _ _ hb _)
end YM.RG05Readout.Planes
