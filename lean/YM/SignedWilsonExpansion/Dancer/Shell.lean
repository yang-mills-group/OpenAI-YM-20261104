import YM.SignedWilsonExpansion.Dancer.Legacy
/-!
# Gram bound on numerical projector strictly before high→own-cap pruning

We avoid relative errors in intermediate Gram comparison (full at h) by continuing
pruning *after* deriving absolute boundedness. Cost only on regulator-removed prescription
samples with detector parameters fitted to filed terminal.Cross.Layer. No
hypothesis of adjoint equivariance of the filed matrix, only its spinning estimate.
-/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.SignedWilsonExpansion.Dancer
open XSpace XSpace.Structure1 Normalize Future Gauge Filter Function Matrix
open SeatsW Commission.Gram Asymptotics Maxwell Maxwell.Free Maxwell.Wick
open scoped BigOperators Topology Classical
-- l no IsCount. convergence.
variable {G:Gauge}{d h n:ℕ}{ι:Type}{l:Filter ι}
namespace Shell
abbrev GramW (G:Gauge)(h:ℕ)(a:Axis):= scene (G:=G) (nodes a) h
abbrev Paar (P:Point G h 2)(x y:Sec G h):= P ![x,y]
lemma actors (P:Point G h 2)(x y:Sec G h): Paar P x y= acts P y x:=rfl
variable (a:Axis)
lemma onPeak (x:Sec G h) (p : Paar (GramW G h a) x (flipE a x)=0): x=0:=by
    let B:=Module.finBasis ℂ (Sec G h); obtain ⟨k,hk,L⟩:= Commission.Adapter.gap _ (prescribed a B); have he : (k* ‖B.equivFun x‖^2 ≤ 0):= (L (B.equivFun x)).trans_eq (congr_arg Complex.re ((cone a B _ x x).symm.trans p)); apply B.equivFun.injective; rw [map_zero]; exact norm_le_zero_iff.mp (by by_contra! v; exact he.not_gt (mul_pos hk (pow_pos v 2)))
def mirrorB (v:Sec G h) := flipE a v
lemma mirror_dual {v:Sec G h} {P:ι→ Sec G h}(H: By ℂ l P v): By ℂ l (fun i=>mirrorB a (P i)) (mirrorB a v):=by
    let f := (Normalize.ori (Signed.reflect a) h).restrictScalars ℝ ∘ₗ reelR (G:=G) h; exact collectReal (translateBy f (payReal H)) -- coercion?
lemma mirror_sub (x y:Sec G h): mirrorB a (x-y)= mirrorB a x - mirrorB a y:=map_sub (flipR (G:=G) a h) x y
variable {x y : Sec G h}{p q:ι→ Sec G h}
structure Emblem (a:Axis)(l:Filter ι)(q:ι→ Point G h 2):Prop where
    approaches (x y:Sec G h) : Tendsto (fun i=> Paar (q i) x y) l (𝓝 (Paar (GramW G h a) x y))
variable {a} {P:ι→ Point G h 2}(hp:Emblem a l P)
include hp
lemma fixed_emit (H:By ℂ l p x)(y:Sec G h): Tendsto (fun i=> Paar (P i) (p i) y) l (𝓝 (Paar (GramW G _ a) x y)) :=by
    apply flowing (A:=fun i=> acts (P i) y) (T:=acts (GramW G _ a) y) (fun t f=> f.continuous_of_finiteDimensional.continuousAt.tendsto.comp (hp.approaches t y)) H (LinearMap.id : ℂ→ₗ[ℂ]ℂ)
lemma p_emit (vp:By ℂ l p x)(vq:By ℂ l q y): Tendsto (fun i=> Paar (P i) (p i) (q i)) l (𝓝 (Paar (GramW G _ a) x y)) := by
    let V{h:ℕ}(x: Sec G h)(P:Point G h 2): Module.Dual ℂ ( Sec G h ):= LinearMap.applyₗ x ∘ₗ acts P; apply flowing (A:=fun i=> V (p i) (P i)) (T:=V x (GramW G _ a)) (fun t f=> f.continuous_of_finiteDimensional.continuousAt.tendsto.comp (fixed_emit hp vp t)) vq (LinearMap.id : ℂ→ₗ[ℂ]ℂ)
lemma emblemY {f:Filter ι}(v:f≤l): Emblem a f P:=⟨fun x y=> (hp.approaches x y).mono_left v⟩
-- throttle full cap from true reflection estimate.NO Rate yet.
variable {t:ℂ}
lemma ordinate (hb:By ℂ l (fun i=> q i-mirrorB a (p i)) 0) (hV:Tendsto (fun i=> Paar (P i) (p i) (q i)) l (𝓝 t)) {σ:Type*}[Fintype σ] (B:Module.Basis σ ℂ ( Sec G h )) : ∃ C:ℝ,∀ᶠ i in l,‖B.equivFun (p i)‖≤ C:=by
    apply throttle; intro U hu hp'
    let ν:= fun i=> ‖B.equivFun (p i)‖; let s (i):ℝ:= (ν i)⁻¹; let v(i):ℂ:= s i; have he:Tendsto s (U:Filter _) (𝓝 0):= tendsto_inv_atTop_zero.comp hp'; have h₀:Tendsto v (U:Filter _) (𝓝 0):=by rw [←Complex.ofReal_zero]; exact Complex.continuous_ofReal.continuousAt.tendsto.comp he
    let X(i):= v i • p i; have hz:(fun i=> ‖B.equivFun (X i)‖)=ᶠ[ (U:Filter _) ] (fun _=> (1:ℝ)):=by
        filter_upwards [hp'.eventually (eventually_gt_atTop (0:ℝ))] with i hi; change _=1; unfold X; rw [map_smul,norm_smul]; exact (congr_arg (·*ν i) ((Complex.norm_real _).trans (Real.norm_of_nonneg (inv_nonneg.mpr hi.le)))).trans (inv_mul_cancel₀ (ne_of_gt hi))
    obtain ⟨x,H⟩:= regroup U B X 1 (hz.mono fun i p=>p.le); let Y(i):= v i • q i; have hY:By ℂ (U:Filter _) Y (mirrorB a x):=by
        refine viaY (x:=mirrorB a x) (by simpa only [zero_smul,zero_add] using addY (scaleY h₀ (monoY hb hu)) (mirror_dual a H)) (Eventually.of_forall fun i=>?_) -- incomplete elaboration
        rw [smul_sub]; let b:=flipR (G:=G) a h; have hv(i): mirrorB a (X i)= v i • mirrorB a (p i):=by rw [show mirrorB a (X i)= b (v i • p i) from rfl,b.map_smulₛₗ]; congr 1; unfold v; simp
        rw [hv,sub_add_cancel]
    have hy : Tendsto (fun i=>Paar (P i) (X i) (Y i)) (U:Filter _) (𝓝 0):=by
        have H(i):Paar (P i) (X i) (Y i)=v i* (v i * Paar (P i) (p i) (q i)):=by simp_rw [actors,X,Y,map_smul,LinearMap.smul_apply,smul_eq_mul]
        simp_rw [H]; simpa only[zero_mul] using h₀.mul (h₀.mul (hV.mono_left hu))
    have ht: x=0:= onPeak _ _ (tendsto_nhds_unique (p_emit (emblemY hp hu) H hY) hy); have HF:= (Stock B H).norm; rw [ht,map_zero,norm_zero] at HF; exact zero_ne_one (tendsto_nhds_unique_of_eventuallyEq HF tendsto_const_nhds hz) -- craft
end Shell
end YM.SignedWilsonExpansion.Dancer
