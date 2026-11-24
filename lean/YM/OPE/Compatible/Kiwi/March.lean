import YM.OPE.Compatible.Kiwi.River
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
local notation "Q"=> LakeT ℓ
variable (u:I→Side)(q:Side)(h:q.val>1) (x y a:Cover)
local notation "Y¤"=> polls u q
abbrev stow (p:I×ℕ): Site (Y¤ p):= Lattice.wrap _ (rangeS q p.2 x)
include h
omit h in
lemma deckSwell (P:Kv)(hP:P≠0)(hp:Ncap u ℓ)(hu:∀ i, Even (u i).val):∀ᶠ i in Q, 4*pdist (decks P (stow u q x i)-stow u q y i+wrap (Y¤ i) a)≥(Y¤ i).val:=by
    let X(i:I×ℕ):= stow u q x i; let Y(i:I×ℕ):= stow u q y i
    filter_upwards [(hp.comp coast₁).eventually (eventually_ge_atTop (a:=4*(size (x-y)+size a)))] with i hi -- nat h variable
    let n:=Y¤ i; let z:= decks P (X i); change n.val≤ 4*pdist (z-Y i+ Lattice.wrap _ a); let B:=z-Y i+Lattice.wrap n a; let K:=ζ q i.2; have ht:n.val/2≤pdist B+size a+K.val*size (x-y):=by
        have hx:=deck_free P hP (X i); apply le_trans hx; have h₁ : separation z (Y i) ≤pdist B+size a:=by
            unfold separation; rw [show z-_ = _ from (show z-Y i=B+(-Lattice.wrap _ a) from by unfold B;abel)] -- _ danger
            apply (pdist_triangle ..).trans; rw [pdist_neg]; exact Nat.add_le_add_left (Next.Free.within_size ..) _
        have h₂ : separation (Y i) (X i)≤K.val*size (x-y):=by
            rw [separation_comm]; change pdist (wrap _ (K.val • x)-wrap _ (K.val • y):Site n) ≤_; rw [←map_sub,← smul_sub]; apply (Next.Free.within_size ..).trans; unfold size; simp only [Pi.smul_apply,nsmul_eq_mul,Int.natAbs_mul, Int.natAbs_natCast]; rw [Finset.mul_sum]
        apply (separation_triangle z (Y i) (X i)).trans (add_le_add h₁ h₂)
    have he : Even n.val:= (hu i.1|>.mul_right _); have hz: n.val=(u i.1).val*K.val:=PNat.mul_coe ..; let L:= (u i.1).val
    have hh:4*(size (x-y)+size a)≤ L:=hi; have hh': 4*(size (x-y)+size a)*K.val≤n.val:=(Nat.mul_le_mul_right K.val hh).trans_eq hz.symm
    have hs:size a≤K.val*size a:= Nat.le_mul_of_pos_left _ K.pos
    have hk:n.val=(n.val/2)*2:=by obtain ⟨r,hr⟩:=he; omega
    change _ ≤ 4*pdist B; nlinarith only [ht,hs,hk,hh']
lemma deckZero (p P:Nestle.Pose)(t:Kv)(hp:t≠0)(ht:Ncap u ℓ)(he:∀ i,Even (u i).val):
     Tendsto (fun i:I×ℕ=>baseR q i.2 ^ (p.heat+P.heat) * tip P (fun a=>paper (reed p t) a (decks t (stow u q x i))) (stow u q y i)) Q (𝓝 0):=by
       simp_rw [forecast,WScale]; let Xa:= stow u q x; let Ya:= stow u q y; rw [show (0:ℝ)= _ from (WZero P (reed p t)).symm]; refine WTends _ _ _ _ ?_; intro D a hD; rw [show p.heat+P.heat=D.length+2 from hD]; let C (i:I×ℕ):= decks t (Xa i)-Ya i+wrap (Y¤ i) a; obtain ⟨B,hB,M,hM⟩:= roof_peck (1/4) (by norm_num) D
       have hv:= ((up_chart u ht).pow (D.length+2)).const_mul B
       apply squeeze_zero_norm' ?_ (show Tendsto (fun i:I×ℕ=>B*Balsam.dew (u i.1)^(D.length+2)) Q (𝓝 0) from by simpa using! hv)
       filter_upwards [(Q_chart u q ht).eventually (eventually_ge_atTop M), deckSwell u q x y a t hp ht he] with i hI hh; rw [norm_mul,Real.norm_of_nonneg (pow_nonneg (ζ_norm _ _) _)]; let d:=D.length+2; have hz: (1/4:ℝ)≤(pdist (C i):ℝ)*Balsam.dew (Y¤ i):=by
           change _≤ _*(sizeR (Y¤ i))⁻¹; rw [←div_eq_mul_inv, div_le_div_iff₀ (by norm_num) (val_pos _),one_mul,mul_comm _ 4]; exact_mod_cast (show (Y¤ i).val≤4*pdist (C i) from hh)
       apply (mul_le_mul_of_nonneg_left (hM _ hI _ hz) (pow_nonneg (ζ_norm ..) _)).trans_eq; rw [mul_left_comm,←mul_pow,ScanCash (n:=u i.1) h]; have hc:= (scans (u i.1) q h).h_pos i.2; change B*(( _ * _)* (scans _ _ h|>.h _ ))^ d=B*_^d; field_simp
include L in
omit u ℓ I x h q y a in
lemma root_point (p v:Reed G) (hp:p.2=v.2): zine v.1 p.1.icicle=Wind p.1 v.1 hull:=by
   let M:= twin (2:Side); have hm(i):Even (M.M i).val:= (show Even (2:Side).val from ⟨1,rfl⟩).mul_right _; have hv:= barometer (L:=L) p v M.M (fun _=>0) M.sides (Eventually.of_forall hm) (show 4 ≤ 4 from le_rfl)
   unfold evenCov at hv; rw [firm, if_pos hp] at hv; simp_rw [bare_entry (L:=L) (h:=le_refl 4),if_pos hp,forecast,sub_self,zero_add] at hv; apply tendsto_nhds_unique hv; refine WTends _ _ _ _ ?_; exact fun D a _=>calm M.M (Eventually.of_forall hm) M.sides a D
-- degenerate marker self
omit h in
lemma stem_zero (p P:Reed G)(ht:Ncap u ℓ)(hv:p.2=P.2)(ℐ:KernelChoices):
   Tendsto (fun i:I×ℕ=>baseR q i.2^(p.1.heat+P.1.heat)*(tip P.1 (fun a=>paper p.1 a (stow u q x i)) (stow u q x i)-firm p P)) Q (𝓝 0):=by
      unfold firm; simp_rw [if_pos hv,root_point (L:=ℐ) p P hv, forecast,sub_self,zero_add,WMinus,WScale]; rw [← WZero P.1 p.1]; refine WTends _ _ _ _ ?_; intro D a hD; rw [hD]; have hh:= star_cost u q 0 a D ht; simpa only [rangeS,smul_zero,zero_add] using! hh -- calc
end YM.OPE.Prairies
