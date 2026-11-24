import YM.OPE.Compatible.Grotto.Fauna
/-!
# Angular phase spectra.Lifting station members multilinearly. erased.B.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Set ContinuousLinearMap Asymptotics
open scoped Topology BigOperators Classical
variable {d k i j s:ℕ}{E:Fin s→Type}{G:ℕ→Type}[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (G i)] [∀ i,NormedSpace ℝ (G i)]
variable {b r x v u:ℝ}{μ:ℕ→ℝ}
local notation "S!"=> Mints E
local notation "L!"=> S! →L[ℝ] S!
variable {T:∀ i: Fin s,Cuts d μ v b (E i) G}
variable {p:(∀ i:Fin s,E i) →L[ℝ] (∀ i:Fin s,E i)}
variable (T) (h:Assist T p)(hk:k<d)(hr:∀ i,ShadeR (T i) (k+1) r)
include h hk hr
variable [∀ i,CompleteSpace (G i)]
-- finite dimensions

noncomputable def cinT (R:L!)(k:ℕ): Fruition R (μ k)→L[ℝ] (Fin s→ G k):= ContinuousLinearMap.pi fun j:Fin s=> (T j).Tap k ∘L ((proj j) ∘L (Fruition R (μ k)).subtypeL) -- remove i
lemma shineZ (j:ℕ)(hj:j≤ s)(v:S!)(hp:v∈ Fruition p (μ k))(hT:forall i: Fin s,i.val<j→ (T i).Tap k (v i)=0): trims j v:=by
    induction j with | zero=> exact trims.be v | succ j ih=> let t:Fin s:= ⟨j,hj⟩; exact (toss T h hk hr t v ⟨hp, ih (by omega) (fun i HI=>hT i (by omega))⟩ (hT t (Nat.lt_succ_self j))).2
lemma shadeE [FiniteDimensional ℝ (G k)]:FiniteDimensional ℝ (Fruition p (μ k)):=by
     let L:= cinT T p k; apply FiniteDimensional.of_injective L.toLinearMap; rw [← LinearMap.ker_eq_bot,LinearMap.ker_eq_bot']; intro v he; refine Subtype.ext ((shineZ T h hk hr s le_rfl v.val v.property ?_).limb); exact fun i _=>congr_fun he i
-- bounded extension uniform from Tap
lemma tintCan [∀ i,CompleteSpace (E i)][FiniteDimensional ℝ (G k)] (i:Fin s) :∃ A:G k→L[ℝ] (Mints E),∀ v:G k, A v ∈ KernNut p (μ k) i.val∧ (T i).Tap k (A v i)=v:=by
     let Z:= KernNut p (μ k) i.val; let L:Z→L[ℝ] G k:=(T i).Tap k ∘L ((proj i)∘L Z.subtypeL); have hx:Surjective L.toLinearMap:=by intro v; obtain ⟨p,hp,ht⟩:=lifty T h hk hr i v; exact ⟨⟨p,hp⟩,ht⟩
     obtain ⟨X,hX⟩:= L.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hx); refine ⟨Z.subtypeL ∘L { X with cont:= X.continuous_of_finiteDimensional},fun v=> ⟨(X v).property,?_⟩⟩; exact LinearMap.congr_fun hX v
-- shift kills first phase
lemma phKill (i:ℕ)(z:Mints E)(hh:z∈ KernNut p (μ k) i): Ux p (μ k) z∈ KernNut p (μ k) (i+1):=by
     let q:=Ux p (μ k); obtain ⟨hy,hT⟩:= hh; have hv: (q^s) z=0:=hy; refine ⟨show (q^s) (q z)=0 from by rw [← byway,← (Commute.self_pow q s).eq,byway,hv,map_zero],?_⟩; have he:Edgewise q:= combe h.arum; change trims (i+1) (q z); by_cases hx:i<s
     · let t:Fin s:=⟨_,hx⟩; have ht:trims t.val z:=hT; apply trims.up t (he _ z hT); rw [scissor he t z ht]; unfold q; rw [byjack]; exact jumpKnow T h hk hr t _ hy hT
     have ht:trims i z:= hT; rw [(ht.drop (Nat.le_of_not_gt hx)).limb, map_zero]; exact fun _ _=> rfl
end YM.OPE.Hark
