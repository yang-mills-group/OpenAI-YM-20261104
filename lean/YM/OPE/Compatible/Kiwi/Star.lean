import YM.OPE.Compatible.Plains.Duel
/-!
# Towers at finite radius. variation parameter for SPD only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Prairies
open Function MeasureTheory Set Topology Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir
open GaussianScore Libra WithLp RG Precision Votive Glass Flume Flume.Script Flock StageLight Balsam Nestle Pert.Full
open Silt Silt.Float Shell Char FreeResolvent Paver Rill Saga Shrew
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {N:Side}{G:Gauge}{L:RG.KernelChoices}{P:ChartRatio G}{d k j r w e m:ℕ} {I:Type}{ℓ:Filter I}
local notation "AX"=> Axis
def scans (n q:Side)(h:q.val>1): Gloam where
    M i:= n*q^i
    q:=q
    growth:=h
    law i:=by rw [pow_succ,←mul_assoc]; rfl
abbrev ζ (q:Side)(i:ℕ):Side := q^i
abbrev rangeS (q:Side)(i:ℕ)(x:Cover): Cover:= (ζ q i).val • x
abbrev stageN (q n:Side)(i:ℕ):Side := n*q^i
def gammaT (n q:Side)(h:q.val>1)(x: Cover): Crew (scans n q h):=⟨(fun i=>wrap _ (rangeS q i x)),fun i=>by
   rw [(((scans ..).ratio _).embed_wrap)]; unfold rangeS ζ; change wrap _ _= wrap _ (q.val • _); simp only [pow_succ', PNat.mul_coe,mul_smul]⟩
def Ncap (f:I→Side)(L:Filter I):= Tendsto (fun i=>(f i).val) L atTop
abbrev baseR (q:Side)(i:ℕ): ℝ:= (ζ q i).val
lemma smoothDoc (q:Side)(h:q.val>1): Tendsto (fun i=>(ζ q i).val) atTop atTop:= by simp_rw [ζ,PNat.pow_coe]; exact tendsto_pow_atTop_atTop_of_one_lt h
lemma ScanCash {q n:Side}(h:q.val>1)(i:ℕ): baseR q i=(scans n q h|>.h i)⁻¹ * Balsam.dew n:=by
   have ht := dew_pos n; change baseR q i=(Balsam.dew (n*q^i))⁻¹*_; rw [Balsam.dew,sizeR, PNat.mul_coe,inv_inv]; unfold Balsam.dew sizeR; have hY:(n.val:ℝ)≠0:= (val_pos n).ne'; push_cast; unfold baseR ζ; push_cast; field_simp
lemma spaceBeam (ℓ: Filter I)(u:I→Side)(hp:Ncap u ℓ) (p q:Cover):∀ᶠ i in ℓ,∀ k:Kv,k≠0→ (decks k (wrap (u i) p))≠ wrap (u i) q:=by
    filter_upwards [hp.eventually (eventually_ge_atTop (2*(size (q-p)+2)))] with i hi b hb
    intro he; have hr:= deck_free b hb (wrap (u i) p); rw [he] at hr; have hz: separation (wrap (u i) q) (wrap (u i) p)≤ size (q-p):=by unfold separation; rw [←map_sub]; exact Next.Free.within_size ..
    omega
lemma xStarts (ℓ: Filter I)(u:I→Side)(hp:Ncap u ℓ)(Z:Side)(h:Z.val>1)(p q:Cover)(hh:p≠q):∀ᶠ i in ℓ,gammaT (u i) Z h p≠gammaT (u i) Z h q:=by
    filter_upwards [hp.eventually (eventually_ge_atTop (1+2*(size p+size q)))] with i hi H
    have he:= congr_fun (congr_arg Subtype.val H) 0; have hv : wrap (u i) p=wrap (u i) q:=by
       let n:=stageN Z (u i) 0; have hh:n.val=(u i).val:=by unfold n stageN;simp; -- cast via avoid by exact lift.
       change wrap n (rangeS Z 0 p) =wrap n (rangeS Z 0 q) at he
       simp only[rangeS,ζ,pow_zero,PNat.one_coe,one_smul] at he
       exact (show wrap (u i) p=wrap (u i) q from _root_.cast (congr_arg (fun n:Side=> (wrap n p=wrap n q)) (Subtype.ext hh)) he)
    exact hh ((gentle (by omega) (n:=u i) (x:=p)).symm.trans ((congr_arg Lattice.lift hv).trans (gentle (by omega))))
lemma reservesP (ℓ: Filter I)(u:I→Side)(hp:Ncap u ℓ)(Z:Side)(h:Z.val>1)(p q:Cover):∀ᶠ i in ℓ,SpareW (gammaT (u i) Z h p) (gammaT (u i) Z h q):=by
    have hf:Ncap (fun i=>stageN Z (u i) 0) ℓ:=by simpa only [Ncap,stageN,pow_zero,mul_one] using! hp
    filter_upwards [spaceBeam ℓ _ hf p q] with i hi; intro j hj; unfold gammaT; dsimp only; unfold rangeS ζ; rw [pow_zero,show (1:Side).val=1 from rfl, one_smul,one_smul]; exact hi j hj
-- Size bill
lemma beamMass (q n:Side)(a x:Cover)(i:ℕ)(hh:2*(size x+size a)+1≤ n.val):
    let N:= stageN q n i
    2*size (rangeS q i x+a)≤ N.val:=by
      intro N; let K:ℕ:= (ζ q i).val; let t:= rangeS q i x; have he: size t=K*size x:=by unfold t size rangeS; simp only [Pi.smul_apply,nsmul_eq_mul,Int.natAbs_mul,Int.natAbs_natCast]; rw [Finset.mul_sum]
      have ht:=(size_add t a).trans_eq (congr_arg (·+size a) he); have hp:N.val=n.val*K:=PNat.mul_coe ..; have hY:0<K:=(ζ q i).pos; rw [hp]; change 2*size (t+a)≤_; nlinarith [Nat.le_mul_of_pos_left (size a) hY, mul_le_mul_of_nonneg_right hh (show 0 ≤ K from Nat.zero_le _),ht]
lemma beamOffset (q:Side)(h:q.val>1)(x a:Cover): Tendsto (fun i=> incVec (Balsam.dew (ζ q i)) (rangeS q i x+a)) atTop (𝓝 (incVec 1 x)):=by
     have he(i:ℕ): incVec (Balsam.dew (ζ q i)) (rangeS q i x+a)= incVec 1 x+Balsam.dew (ζ q i) • incVec 1 a:=by
           unfold rangeS; ext1 k; simp [incVec,nsmul_eq_mul]; unfold Balsam.dew sizeR; have hY:((ζ q i).val:ℝ)≠ 0:=(val_pos _).ne'; field_simp; unfold ζ; push_cast; ring
     simp_rw [he]; let X:=smoothDoc q h; have ht:Tendsto (fun i=> Balsam.dew (ζ q i)) atTop (𝓝 0):=tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp X); simpa using! tendsto_const_nhds (x:=incVec 1 x)|>.add (ht.smul_const _)
end YM.OPE.Prairies
