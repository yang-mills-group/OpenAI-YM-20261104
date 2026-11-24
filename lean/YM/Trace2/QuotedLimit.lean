import YM.Trace2.Quoted
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 240000
set_option maxRecDepth 5000
noncomputable section
namespace YM.Trace
open Set Function Filter Table MeasureTheory YM.Work.A01 Analysis OPE MergeProof.Ribbons Columns
open Wilson MergeProof RG Extraction Bid Push.RelayDifference Next.UVStress Next.Rank Further.CorrectedLift
open MergeProof.East Next.Extract Dash Cells Climb Ward Org Maxwell Labels UVNext.FreeStress
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{S:Table C.book} {f:Extraction.Order}
local notation "B"=> Bel C.book
local notation "v"=> scalarLabel C.labels
variable (F:Spec.Final C f S) (u:Services C f S)
variable (P:MaxwellData C)(g:QuotedWeak C f)

lemma total_identity : (↑4:ℂ) • v = total C.labels:= by convert (scalar_actual C.labels).symm using 1; simp [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
lemma freeTotal_conj : (B).conj P.hT.spin 4 (total C.labels) = total C.labels:=by
    change (B).conj _ 4 (∑ a,panel C.labels a a)= _; rw [map_sum]; exact Finset.sum_congr rfl (fun i _=> panel_star ..)
lemma freeScalar_conj : (B).conj P.hT.spin 4 v = v:=smul_right_injective ((B).Field 4) (show (4:ℂ)≠0 by norm_num) (calc
    (4:ℂ) • (B).conj P.hT.spin 4 v = (B).conj P.hT.spin 4 ((4:ℂ) • v) := by rw [map_smulₛₗ,show (starRingEnd ℂ) 4=4 from map_ofNat ..]
    _ = total C.labels := (congr_arg _ total_identity).trans (freeTotal_conj P)
    _ = _ := total_identity.symm)
lemma freeScalar_mirror (k:Signed) : (B).mirror P.hT.spin 4 k v=v:= smul_right_injective ((B).Field 4) (show (4:ℂ)≠0 by norm_num) (calc
    (4:ℂ) • (B).mirror P.hT.spin 4 k v = (B).mirror P.hT.spin 4 k ((4:ℂ) • v) := (map_smul ..).symm
    _ = total C.labels := (congr_arg _ total_identity).trans (total_transfer C.labels P.hT.spin k)
    _ = _ := total_identity.symm)

lemma quoted_scalar_subsequence {W:ℕ→Wheel C 4} (hW:RA W f P.hT.spin):
  ∃ k:ℕ→Filter Cutoffs,∃ x:ℕ→C.label 4,(∀ᶠ i in atTop, NeBot (k i) ∧ k i≤ f.fuse ∧
      Tendsto (fun j:Cutoffs=>(W i).atCut j ⟨4,by decide⟩ (v:(B).Field 4)) (k i) (𝓝 (x i))) ∧
      (∀ᶠ i in atTop,(∀ s,S.mirror F.room.kernel.spin 4 s (S.project 4 (x i))=S.project 4 (x i))∧ S.conj F.room.kernel.spin 4 (S.project 4 (x i))= S.project 4 (x i)):=by
    have hT:∀ᶠ i in atTop, ∃ ℓ : Filter Cutoffs,∃ x:C.label 4,ℓ.NeBot ∧ ℓ ≤ f.fuse ∧
        Tendsto (fun j:Cutoffs=>(W i).atCut j ⟨4,by decide⟩ (v:(B).Field 4)) ℓ (𝓝 x) ∧
        (∀ s,S.mirror F.room.kernel.spin 4 s (S.project 4 x)=S.project 4 x) ∧ S.conj F.room.kernel.spin 4 (S.project 4 x)= S.project 4 x:=by
       filter_upwards [hW.grants,hW.real,hW.h_symm] with i hi hr hs
       obtain ⟨c,hc⟩:=hi
       have hc : ∀ᶠ j in f.fuse, ‖(W i).atCut j‖ ≤ c:=Order.fused f _ |>.2 hc
       obtain ⟨ℓ,hℓ,hL,y,hy⟩:=finite_extract _ _ hc
       set z:Fin (4+1) := ⟨4,(by decide:4<4+1)⟩; let x:= y z v
       let H:=fun j=>(W i).atCut j z v
       have hp:Tendsto H ℓ (𝓝 x):= Dash.arcing (tendsto_pi_nhds.mp hy z) (tendsto_const_nhds (x:=(v:(B).Field 4)))
       have hr : ∀ᶠ j in f.fuse, ∀ d q,(W i).atCut j d ((B).conj P.hT.spin d q) = star ((W i).atCut j d q) := (Order.fused f _).2 hr
       have hs : ∀ᶠ j in f.fuse, ∀ d s q,(W i).atCut j d ((B).mirror P.hT.spin d s q) = (C.book.mirrorGroup d s) ((W i).atCut j d q):=(Order.fused f _).mpr hs
       use ℓ,x,hL,hℓ,hp
       constructor
       · intro k
         let A: C.label 4 →ₗ[ℂ] C.label 4:=C.book.mirrorGroup 4 k
         have he: Tendsto (fun j=>A (H j)) ℓ (𝓝 (A x)):= A.continuous_of_finiteDimensional.continuousAt.tendsto.comp hp
         have hh:= tendsto_nhds_unique_of_eventuallyEq he hp ((hs.filter_mono hℓ).mono (fun j hj=> (congr_arg _ (freeScalar_mirror P k).symm).trans (hj z k v) |>.symm))
         exact (S.mirror_project F.room.kernel.spin 4 k x).trans (congr_arg (S.project 4) hh)
       have he:= (by fun_prop : Continuous fun u:C.label 4=> star u).continuousAt.tendsto.comp hp
       refine (S.conj_project F.room.kernel.spin 4 x).trans (congr_arg (S.project 4) (tendsto_nhds_unique_of_eventuallyEq he hp ?event))
       case event=> exact (hr.filter_mono hℓ).mono (fun j hj=> ((hj z v).symm.trans (congr_arg _ (freeScalar_conj P))))
    choose n hn using eventually_atTop.mp hT
    choose! k x hk using hn
    exact ⟨k,x,(eventually_ge_atTop n).mono (fun b hb=> (hk b hb).imp_right (And.imp_right fun t=>t.1)), (eventually_ge_atTop n).mono (fun b hb=> (hk b hb).2.2.2)⟩ -- And.imp_right name?
end YM.Trace
namespace YM.Trace
open Set Function Filter Table MeasureTheory YM.Work.A01 Analysis OPE MergeProof.Ribbons Columns
open Wilson MergeProof RG Extraction Bid Push.RelayDifference Next.UVStress Next.Rank Further.CorrectedLift
open MergeProof.East Next.Extract Dash Cells Climb Ward Org Maxwell Labels UVNext.FreeStress
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G} {f:Extraction.Order}{S:Table C.book}
local notation "B"=> Bel C.book
local notation "v"=> scalarLabel C.labels
variable (F:Spec.Final C f S) (u:Services C f S) (P:MaxwellData C)
lemma boil_small : Tendsto (fun s:ℝ=>Perch.boil s/s) atTop (𝓝 0):= by
   have hz:=Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
   have h:=(Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2 |>.comp Perch.y_rate) |>.mul hz; rw [mul_zero] at h
   apply h.congr'; filter_upwards [eventually_gt_atTop (1:ℝ)] with i hi
   change (Perch.y i ^ 2 * Real.exp (-Real.log (Real.log i))) * (Real.log i / i) = _
   rw [Real.exp_neg,Real.exp_log (Real.log_pos hi)]; unfold Perch.boil; field_simp [(Real.log_pos hi).ne', hi.ne']
lemma boil_energy (hg : G.Simple): Tendsto (fun s=>(Perch.boil (C.path.levels.clock.hatBeta s) / C.S.scale s)) atTop (𝓝 0):= by
   let A:=C.path.levels; let Q:= A.clock
   have hS:Tendsto (fun s=> Q.hatBeta s / C.S.scale s) atTop (𝓝 G.slopeConstant):=by
      simp_rw [Calendar.hatBeta,show Q.schedule=C.S from rfl,add_div]; apply ((Tendsto.div_atTop (tendsto_const_nhds (x:=Q.bar)) C.S.divergent).add ((tendsto_const_nhds (x:=G.slopeConstant)).congr' ((C.S.divergent.eventually_gt_atTop 0).mono (fun i hi=>(mul_div_cancel_right₀ _ hi.ne').symm)))) |> (by simpa using ·)
   have h:=((boil_small.comp (Station.hat_rate A hg)).mul hS); rw [zero_mul] at h; apply h.congr (fun i=>?_ ) -- no such lemma?
   have hx : (Q.hatBeta i)≠0:=((show 1<Q.hatBeta i from A.fits.delayed _).trans' zero_lt_one).ne'
   change Perch.boil (Q.hatBeta i)/(Q.hatBeta i) * (Q.hatBeta i / C.S.scale i) = Perch.boil (Q.hatBeta i)/(C.S.scale i); rw [div_mul_eq_mul_div]; field_simp
lemma billboard (b:ℝ)(hg:G.Simple) {k:ℕ→ℕ}(hk:Tendsto k atTop atTop) : RateIs atTop (fun s=> C.S.scale (k s)) (fun s=> Perch.bill b (Atlas.clim C.path.levels (k s))) 0:= by
    apply RateIs.exp'
    have he:=((boil_energy (C:=C) hg).comp hk).mul_const b; change Tendsto (fun s=>_) atTop _
    simpa only [Function.comp_apply, zero_mul, mul_div_right_comm] using! he
include F u
lemma quoted_scalar_cheap (g:QuotedWeak C f)(R:ℝ)(hR:0<R):
   ∃ W:ℕ→Wheel C 4,∃ k:ℕ→Filter Cutoffs,∃ x:ℕ→C.label 4,
     Tendsto (fun i=> (W i).r) atTop (𝓝 0) ∧ Granular W f P.hT.spin 2 R ∧ (∀ᶠ i in atTop, (k i).NeBot ∧ k i≤f.fuse∧Tendsto (fun j=>(W i).atCut j ⟨4,by decide⟩ v) (k i) (𝓝 (x i))) ∧
     (∀ᶠ i in atTop,(∀ s,S.mirror F.room.kernel.spin 4 s (S.project 4 (x i))=S.project 4 (x i))∧ S.conj F.room.kernel.spin 4 (S.project 4 (x i))= S.project 4 (x i)) ∧
     ∀ ε:ℝ,0<ε→0<4-ε→ Tendsto (fun i=> ‖centering S 4 (S.project 4 (x i))‖ / ((W i).r^(4-ε:ℝ))) atTop (𝓝 0):=by
    obtain ⟨b,c,hb,k',hk,Y,hW,hY⟩:=g R hR P.hT.smooth P.hT.spin
    let W:= fun i=> wok C 4 (k' i) b c (Y i)
    change Granular W _ _ _ _ at hW
    have hg:=u.simpleGate
    obtain ⟨k,x,hk₁,hk₂⟩:=quoted_scalar_subsequence F P hW.toRA
    refine ⟨W,k,x,hW.small,hW,hk₁,hk₂,fun ε hε hε4=>?_⟩
    let K := ((centering S 4).comp (S.project 4)).toContinuousLinearMap
    let a:= fun i=>C.S.scale (k' i); let Z:=fun i=> Atlas.clim C.path.levels (k' i)
    let t:=fun i=>(W i).r; have hr(i) : 0<t i:=(W i).rad
    have hu(i): C.S.a (k' i) ≤ t i := by
      change C.S.a (k' i) ≤ C.S.a (k' i) * Station.mag C.path.levels b (k' i)
      rw [Atlas.mag_bill]; exact le_mul_of_one_le_right (C.S.a_pos _).le (Real.one_le_exp (mul_nonneg (Perch.boil_pos _) hb.le))
    let D(i):=fare C (k' i) 4 3; let s:= b*4+ Atlas.saves C 4
    have htC (i):0 ≤ (C.S.a (k' i))^4:= pow_nonneg (C.S.a_pos _).le _
    have hp:= C.S.divergent.comp hk
    have hP:(∀ᶠ i in atTop, ‖K (x i)‖ ≤ ‖K‖ * D i * C.S.a (k' i)^4 * Perch.bill s (Z i)) := by
       let v₀:= ladder C 4 v; obtain ⟨W',r',L,δ⟩:=u.purchase; obtain ⟨Ac,V,E,H',h'⟩:=u.along
       filter_upwards [hk.eventually (Atlas.income b hb u.simpleGate F.room.cutoff v₀),hk₁] with i hi ⟨ha,hL,hx⟩
       have hv:= (hY i).1
       let y(j:Cutoffs) := (W i).atCut j ⟨4,by decide⟩ v
       have he: ∀ᶠ j in k i, Next.UVStress.quota C 4 (k' i) j.1 j.2 (y j) ≤ C.S.a (k' i)^4*Perch.bill s (Z i):= by
          filter_upwards [hL ((Order.fused f (fun j=>k' i< j.1)).mpr (show f.late fun n _=> k' i<n from Eventually.of_forall fun m=>f.mesh.cofinal.eventually (eventually_gt_atTop (k' i))))] with j hj
          change k' i < j.1 at hj
          specialize hi j.1 j.2 hj.le _ (hY i|>.2 j.1 j.2 hj) (y j) ((Next.Rank.East.poured F.room.cutoff hv hj.le _ _ (hY i |>.2 _ _ hj) _))
          let l:= C.S.a (k' i); let z:=Price.awake C 4 (k' i) j.1 j.2 (y j)
          have heq : Price.columns C 4 (k' i) j.1 j.2 (y j)= (↑(l^4):ℂ) • z:=by
             unfold z Price.awake l; push_cast;rw [smul_smul,mul_inv_cancel₀ (pow_ne_zero 4 (Complex.ofReal_ne_zero.mpr (C.S.a_pos (k' i)).ne')),one_smul]
          change (C.labels.level 4).coeffSize (Price.columns C 4 (k' i) j.1 j.2 (y j)) ≤ _; rw [heq]
          have hmul(a:ℂ)(x:C.label 4): (C.labels.level 4).coeffSize (a•x)= ‖a‖ * (C.labels.level 4).coeffSize x:=by
             unfold Labels.Frame.coeffSize; simp only [Finset.mul_sum,Pi.smul_apply,norm_smul]
          rw [hmul,Complex.norm_real,Real.norm_of_nonneg (htC i)]
          apply mul_le_mul_of_nonneg_left _ (htC i)
          exact (le_mul_of_one_le_left (show 0 ≤ (C.labels.level 4).coeffSize z from Finset.sum_nonneg fun i _=>norm_nonneg (z i)) (Real.one_le_exp (by exact Perch.boil_pos _))).trans hi
       obtain ⟨y',hy',hx'⟩:=limit_cap δ.toTableTickets u.simpleGate h' F.phase.transport.injection (d:=4) (show 3<4 by decide) y _ (hk:=hv) hL he hx
       obtain ⟨z,hz⟩:=hy'
       obtain ⟨w,hw'⟩ := first_grade F u.simpleGate (d:=3) (by decide) z
       have hb' : K (x i) = K (x i-y'):=by
         rw [map_sub]; suffices K y'=0 from (this ▸ (sub_zero _).symm)
         dsimp only [K,LinearMap.coe_toContinuousLinearMap',LinearMap.comp_apply]; rw [←hz,hw',map_smul,F.sector.derivatives.fixs F.phase.transport.injection F.room.kernel.laws,map_smul,const_out F.room.kernel.laws,smul_zero] -- unknown
       rw [hb']; exact (K.le_opNorm _).trans ((mul_le_mul_of_nonneg_left hx' (norm_nonneg _)).trans_eq (by unfold D; ring))
    obtain ⟨W',r',L,δ⟩:=u.purchase
    have hD: RateIs atTop a D 0:= by convert! fare_rate δ.toTableTickets (x:=1) hk hp (tendsto_const_nhds.congr' ((hp.eventually_gt_atTop 0).mono fun i hi=> (div_self hi.ne').symm)) using 1; first | rfl | norm_num
    have hS: RateIs atTop a (fun i=> C.S.a (k' i)) (-1):= by convert rescale (Ribbons.Note.note_a C.S) (x:=1) hk (tendsto_const_nhds.congr' ((hp.eventually_gt_atTop 0).mono fun i hi=>(div_self hi.ne').symm)) using 1 <;> first | rfl | norm_num
    have he := ((((RateLE.const (l:=atTop) ‖K‖ hp).mul (hD.pays hp)).mul ((hS.rpow ε).pays hp)).mul ((billboard s hg hk).pays hp)).of_norm_le (F:=fun i=> ‖K (x i)‖ / (t i)^(4-ε)) (by
       filter_upwards [hP] with i hi; rw [Real.norm_eq_abs,abs_of_nonneg (by positivity [hr i])]; apply (div_le_div_of_nonneg_right hi (by positivity [hr i])).trans
       let c:=C.S.a (k' i); have hc := C.S.a_pos (k' i); have hnt:=Real.rpow_le_rpow hc.le (hu i) hε4.le
       apply (div_le_div_of_nonneg_left (show 0 ≤ ‖K‖ * D i * c^4 * (Perch.bill s (Z i)) from by unfold D Perch.bill; exact mul_nonneg (mul_nonneg (mul_nonneg (show 0 ≤ ‖K‖ from ContinuousLinearMap.opNorm_nonneg K) (fare_pos ..).le) (htC i)) (Real.exp_pos _).le) (Real.rpow_pos_of_pos hc _) hnt).trans_eq
       change ‖K‖*D i*c^4*_ / c^(4-ε) = _ * c^ε * _
       have heq : c^4/c^(4-ε)= c^ε := by rw [show c^(4:ℕ)=c^(4:ℝ) from (by simpa only [Nat.cast_ofNat] using! (Real.rpow_natCast c 4).symm), ← Real.rpow_sub (by positivity : 0<c)]; ring_nf -- fix lemma
       apply (show ‖K‖*D i*c^4*Perch.bill s (Z i) / c^(4-ε) = (‖K‖*D i)*(c^4/c^(4-ε))*Perch.bill s (Z i) by ring).trans
       rw [heq]) -- coercions
    exact he.tends (by linarith only [hε]) hp
end YM.Trace
