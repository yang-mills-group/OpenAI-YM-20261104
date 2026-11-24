import YM.Pert.Weak
import YM.Next.MAXWELL.Lit
import YM.RG12.Canonical.Low
/-!
# Ward current calibration for *any* persistent quantitative zoom under Final

Unlike using a particular ActLaw/Scaling choice, this gives a meter-precision route
under just Approaches/Stable on new joint lamps. Pin one MaxwellData for the whole
procedure. We only need a subsequence orientation; C & physical phases/order unchanged.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Kintsugi
open Function Set Filter Org Spec Climb Table Next.UVStress UVNext.FreeStress
open scoped Topology BigOperators ContDiff
variable {G:Gauge}{C:Family G}{S : Table C.book}{f : Extraction.Order}(U : Final C f S) (T : MaxwellData C)
local notation "H"=>U.room.kernel
local notation "V"=>U.sector.derivatives
local notation "B"=> Bel C.book
local notation "jU"=>U.sector.energy
local notation "Jc"=>reCenter S (jU)
local notation "Q"=>U.phase.transport
-- independent supply, signed normalization does not matter
include C in
lemma oracle (hG:G.Simple):∃ T:MaxwellData C,T.T.J=torch C.book.grid 1 ∧ FreeDiv T.T T.hT T.lit.hers:=by
   obtain ⟨T,-⟩:= Maxwell.Free.maxwell_supplies C hG 1 one_ne_zero
   obtain ⟨P,h,-,-,-,-,-,hV⟩:=fire hG T 1 one_ne_zero
   exact ⟨P,h,hV⟩

lemma recollect : Jc ∈ KernelSpace (H|>.spin):=
   enters (H) _ (sym_mem.mpr ⟨(Q).conserved.symmetric,(Q).conserved.real,fun s i j=>by rw [← (Q).spots.signed];exact (Q).spin ..⟩)
lemma centered_cons : Conserved (V) (H|>.spin) (Jc):=by
   obtain ⟨he,hv,-⟩:=sym_mem.mp (kernel_mem.mp (recollect U)).1
   refine ⟨he,hv,fun i=>?_⟩
   change ∑ j, (V).deriv 4 j (centering S 4 (jU j i))=0
   have e:=(V).unit_drop (H|>.laws) (Q).derivatives (H|>.smooth) 4
   simp_rw [value_center,map_sub,map_smul,e,smul_zero,sub_zero,(Q).conserved.divergence]
lemma centered_flux : StressLaws S (Jc) (V|>.deriv) U.sector.turns.lie:=by
   let t i j := -expectation S 4 (jU i j)
   rw [show Jc = jU + fossil t from ?_]
   exact add_unit (H) (Q|>.charges) t (fun i j=> by dsimp [t]; rw [(Q).conserved.symmetric])
   funext i j; change centering S 4 (jU i j)=jU i j+t i j • S.unit _; simp [value_center,t,sub_eq_add_neg]

variable (X : Scaling S)
local notation "Z"=> Approaches (path X) (isoPanel X)
set_option quotPrecheck false
local notation "R"=> Stable (H|>.spin) T.hT.spin (V) T.T.W X
include T
lemma center_ne (h : Z) : (Jc) ≠ 0 :=
   Extra.WeakScaling.flux_nontrivial (H) (Jc) (centered_flux U) (fun hw=> T.lit.born (by
     ext1 a; ext x
     have hl:= bend_limit (H) (Q).derivatives T.hT T.lit.pales X 4 a h
     have he (k:ℕ):tiltScale X (V) k 4 a=0:=by unfold tiltScale; rw [hw]; change X.r k • (X.carry k (0 : _ →L[ℂ] _)) = 0; ext v; change X.r k • (X.U k 5).symm (0 : S.Field 5) = 0; rw [map_zero,smul_zero]
     simp only [he] at hl
     exact DFunLike.congr_fun (tendsto_nhds_unique hl tendsto_const_nhds) _))

lemma normal_chart {c : ℝ} (hc : c ≠ 0) 
    (h:Z)(r:R) (hx:X.meter (c • Jc) T.T.J) :
    Tendsto (fun k=> labelScale X k (Jc)) atTop (𝓝 ((T.T.κ)⁻¹ • T.T.J)):=by
  have hk : Conserved (V) (H|>.spin) (c • Jc) := (linear_cons (V) (H|>.spin) (Q).rights (c • (⟨Jc,recollect U⟩ : KernelSpace (H|>.spin)))).1 (by
     rw [map_smul,(linear_cons _ _ _ _).2 (centered_cons U),smul_zero])
  have hK : StressLaws S (c • Jc) (c • (V|>.deriv)) (c • U.sector.turns.lie) := by
     have h0:= scale_stress (H) (centered_flux U) c
     rw [Complex.coe_smul] at h0; exact h0
  let I : IR (C:=C) S := {J:=c • Jc, p:=c • (V|>.deriv), Y:=c • U.sector.turns.lie}
  have hpre : Pre (H) (V) (c • Jc) (c • (V|>.deriv)) (c • U.sector.turns.lie):=
     ⟨hk,(sym_mem.mp (kernel_mem.mp ((KernelSpace (H|>.spin)).smul_mem c (recollect U))).1).2.2,hK⟩
  have hl : leaves I.p 4 = c • leaves (V|>.deriv) 4:= by ext i x; rfl
  obtain ⟨D0,N,m,R0,hR,hW⟩:=(Extra.WeakScaling.tracks_ratio T (I:=I) (H) (Q).injection (Q).derivatives hpre hl).ask
  obtain ⟨k,hk⟩:= focused_track (H) (Q).derivatives T.hT T.T T.lit.pales X h r _ hx N D0 m R0 hR
  have he : Tendsto (fun i => c / X.xi i) atTop (𝓝 T.T.κ) := (tendsto_add_atTop_iff_nat k).mp (hW (afterScale X k) D0 N m R0 le_rfl le_rfl le_rfl le_rfl hk)
  refine tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=> ?_
  refine ((he.inv₀ T.T.hκ).smul (hx i j)).congr ?_; intro k
  change (c / X.xi k)⁻¹ • (X.U k 4).symm (((↑((X.xi k)⁻¹ * X.r k^4):ℂ)) • (c • ((Jc) i j))) = _
  rw [Complex.coe_smul, ← show ∀ v, (X.U k 4).symm ((c/X.xi k)⁻¹ • v)=(c/X.xi k)⁻¹ • (X.U k 4).symm v from ((X.U k 4).symm.toLinearMap.restrictScalars ℝ).map_smul ((c/X.xi k)⁻¹), smul_smul, smul_smul]
  change (X.U k 4).symm _= (X.U k 4).symm _
  congr 2
  field_simp [hc,(X.sign k).ne']
-- Fast collapse on every path via compact calibration of the nonzero stress line.
lemma persistent (hT:FreeDiv T.T T.hT T.lit.hers) (h:Z)(r:R) : ∃ q : Extraction.Sequence,
    Tendsto (fun k=> labelScale X (q k) (Jc)) atTop (𝓝 ((T.T.κ)⁻¹ • T.T.J)):=by
  have hn:= center_ne U T X h
  obtain ⟨p,Y,hy,hp⟩:= subsector X (Jc) T.T.J hn hT.sign
  let X':=narrow X p _ (fun k=>positive_strength X (p k) hn hT.sign)
  have h':=narrow_path X p _ (fun k=>positive_strength X (p k) hn hT.sign) h
  have r':=narrow_stable X p _ (fun k=>positive_strength X (p k) hn hT.sign) r
  obtain ⟨w,hB,hC⟩:= on_axis X' (H) (Q).derivatives (Q).rights (⟨Jc,recollect U⟩: KernelSpace (H|>.spin))
    ((linear_cons ..).2 (centered_cons U)) T.hT T.lit.pales T.lit.hers h' r' Y hp
  obtain ⟨c,hc⟩:= (finrank_eq_one_iff_of_nonzero' (⟨(⟨T.T.J,hT.enters⟩:KernelSpace T.hT.spin),(linear_cons ..).2 hT.origin⟩ : LinearMap.ker (currentDiv T.T.W T.hT.spin T.lit.hers))
      (fun e=> hT.sign (congr_arg (fun v:LinearMap.ker _=>v.val.val) e))).mp hT.one ⟨w,hC⟩
  have he : c • T.T.J = Y:=(congr_arg (fun v : LinearMap.ker (currentDiv T.T.W T.hT.spin T.lit.hers)=> v.val.val) hc).trans hB
  have HN : c≠0:= by
     intro hc; rw [hc,zero_smul] at he; exact hT.sign (norm_eq_zero.mp (hy.symm.trans ((congr_arg norm he.symm).trans norm_zero)))
  have hm : X'.meter (c⁻¹ • (Jc)) T.T.J := by
    intro i j
    have ht (i j:Axis) := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (show Tendsto (balanced_J X' (Jc)) atTop (𝓝 Y) from hp) i) j
    have heij : T.T.J i j= c⁻¹ • Y i j:=by rw [← he]; exact (inv_smul_smul₀ HN _).symm
    rw [heij]
    refine ((ht i j).const_smul c⁻¹).congr fun k=>?_
    apply (X'.U k 4).injective
    rw [LinearEquiv.apply_symm_apply,RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul,balanced_value,Pi.smul_apply,Pi.smul_apply,RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_comm]
  exact ⟨p,normal_chart U T X' (inv_ne_zero HN) h' r' hm⟩
end YM.RG12.Kintsugi
