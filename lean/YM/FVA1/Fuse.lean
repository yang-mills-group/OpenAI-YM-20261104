import YM.FVA1.Stock
import YM.Extra.MULTISOURCE_TRAJECTORIES.Algebra

/-! Algebra check with exact link evaluations and the original predicates.
All tSums involving virtual markers in the decoder are on finite marker rings
but potentially infinite gas and regular dictionaries; show summability first. -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA1.Stock
open MeasureTheory Finset Function Filter Lattice Wilson RG RG05.Strand Extra.Trajectories
open Marker Overlay Overlay.GapsLocal Push.GridApprox.Nil MergeProof Accent
open Push Push.AbsoluteSums
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {I J V T:Type}[DecidableEq I][Fintype I][DecidableEq V]
variable {G:Gauge}{n:Side}(D:Stock (n:=n) I J G)(P:RG.Rep G n){Γ:Census V}
variable (tag:I→Γ.Mode)(read:I→(V→T)→ℂ)(o:Positions V n)(header : V→(V→T)→ℂ)

local notation "W"=> D.reinsert P tag read o header

def glass0 (i:J)(U:Config G n) :Poly (FreeCensus I) := Poly.inject fun z=> masked P.p.threshold (D.X i) (D.bin i z) U
def packet0 (i:Finset ℕ)(U:Config G n):Poly (FreeCensus I):= if P.activities.admissible P.p U i then ∏ j∈i,D.hard j U else 0
def density0 (U:Config G n) : Poly (FreeCensus I):= (Real.exp (P.exponent U):ℂ) • (Poly.pass (∑' i,D.glass0 P i U)*∑' i,D.packet0 P i U)

variable {ρ:I→ℝ}{fee a b F v κ:ℝ}
omit [DecidableEq V] in
lemma sides (h:D.Room P)(hL:D.Lent P ρ fee a b)(x:Config G n): Summable (fun i=>D.glass0 P i x) ∧ Summable (fun i=>D.packet0 P i x) ∧
    (∑' i,D.glass0 P i x).part (FreeCensus I).quiet=0:=by
  obtain ⟨u,hu,hP,hF⟩:=hL.paints; let e i:= wordsPrice ρ (u i)
  let s i:=D.glass0 P i x; let S i:=D.packet0 P i x
  have ht:= Film.hit_sum D.X P.p.B hP (P.p.exponent_pos.le.trans hL.extraS) (fun i=>Film.sum_words_pos _ hL.radius _ (hu i)) h.stays
  have hh:Summable s:= by
    refine (Poly.budgeted hL.radius ht ?_).1; intro i
    refine Finset.sum_le_sum fun j _=> mul_le_mul_of_nonneg_left ?_ (Poly.worth hL.radius _).le
    change ‖masked P.p.threshold _ _ x‖ ≤ u i j; by_cases H: Healthy P.p.threshold (D.X i) x
    · obtain ⟨k,hk⟩:= h.stays i; rw [masked_eq _ _ _ _ H]; exact (hF i j k hk).2 x H [] (by simp) (by simp)
    rw [masked_ne _ _ _ _ H,norm_zero]; exact hu i j
  refine ⟨hh,?_, ?_⟩
  · obtain ⟨K,hK,-,hC⟩:=hL.hasK; choose r hr hX hx using hC
    have hp(ι): Poly.price ρ (D.hard ι x) ≤ K ι:= (Finset.sum_le_sum (s:=univ) (f:=fun i=> _ * ‖(D.hard ι x).part i‖) (g:=fun i=> Poly.toll ρ i * r ι i) fun i _=> mul_le_mul_of_nonneg_left (hX ι x i) (Poly.worth hL.radius i).le).trans (hx _)
    have hQ(i):0 ≤ K i:= (Poly.nonnegative hL.radius _).trans (hp i)
    have hz:= summable_finsetProd_of_summable_nonneg hQ hK
    refine (Poly.budgeted hL.radius hz ?_).1; intro i; unfold packet0; split
    next h=> exact (Poly.multiple hL.radius ..).trans (Finset.prod_le_prod (fun i _=>Poly.nonnegative hL.radius _) (fun i _=> hp _))
    next _=> rw [Poly.zero_price]; exact prod_nonneg fun i _=>hQ _
  rw [Poly.share hh]; change ∑' i,masked P.p.threshold (D.X i) (D.bin i (FreeCensus I).quiet) x=0; simp_rw [h.silent]; simp [masked]

lemma decode_glass (x:V→T) (i:J)(u:Config G n) : decoder tag (fun j=>read j x) (D.glass0 P i u)= (W).glass x i u:=by
  ext z
  by_cases h:Healthy P.p.threshold (D.X i) u; swap
  · rw [show D.glass0 P i u=0 from (by ext z; exact masked_ne _ _ _ _ h),map_zero, Poly.part_nil]
    exact (masked_ne P.p.threshold _ _ u h).symm
  change _=masked P.p.threshold (D.X i) (decSum tag read (D.bin i) x z) u
  rw [masked_eq _ _ _ _ h,decSum_eq];
  rw [show D.glass0 P i u=Poly.inject (fun z=> D.bin i z u) from by
        ext z; exact masked_eq _ _ _ _ h]

lemma decode_packet (h:∀ i,(tag i).val.Nonempty)(x:V→T)(i:Finset ℕ)(u:Config G n): decoder tag (fun j=>read j x) (D.packet0 P i u)= (W).packet x i u:=by
  unfold Film.packet packet0; split
  next hh => exact paint_many _ (leafName_sq tag _ h) free_all ..
  next hh => exact map_zero _

lemma exact_reinsert [Fintype V](h:∀ i,(tag i).val.Nonempty)(x:V→T)(u:Config G n)(hR:D.Room P)(hL:D.Lent P ρ fee a b):
    (W).density x u=Poly.pass (Mach Γ (fun i=>header i x)) * decoder tag (fun j=>read j x) (D.density0 P u):=by
    let φ:=decoder tag (fun j=>read j x); let F:=φ.toContinuousLinearMap; let i:= Mach Γ (fun i=>header i x)
    obtain ⟨hh,hp,hX⟩:=D.sides P hR hL u
    have hz : ∑' j,(W).glass x j u=φ (∑' j,D.glass0 P j u):=by
        simp_rw [← D.decode_glass P tag read o header x]; exact (F.map_tsum hh).symm
    have ht : ∑' j,(W).packet x j u=φ (∑' j,D.packet0 P j u):=by
        simp_rw [← D.decode_packet P tag read o header h x]; exact (F.map_tsum hp).symm
    have hM:i.part Γ.quiet=0:=Accent.mute ..
    unfold density0; change (Real.exp (P.exponent u):ℂ) • (Poly.pass (i+ (∑' j,(W).glass x j u))*_) = _
    rw [hz,pass_add hM ((dec_quiet tag _ h _).trans hX),ht]
    unfold φ; rw [map_smul,dec_mul _ _ h,dec_pass _ _ h _ hX,mul_assoc,mul_smul_comm]

end YM.FVA1.Stock
