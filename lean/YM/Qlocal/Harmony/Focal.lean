import YM.Qlocal.Dialect.Palette
/-!
# Multilinear behavior of one stencil in Fk pose authentication.

Use the `V`-alphabet prescription. We can give symbols in the tentative epoch
contribution *weights* depending on the tests without making a new estimation
problem for each input. The algebra facts here concern the recognition of forecast
postures (not K budgets). No clipping/normalization/error subtraction disguised as
polynomial coefficients: these use `Symmetry.Orbit.words`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Harmony.Focal
open Function Finset Filter Set Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Marker MeasureTheory Extra.Trajectories
open Comparison Comparison.RG02 Bulk Dialect Reckoner
open Matrix Push Uniform SectorMeasure PhysicalNext Next.Fluctuations Next.SectorChange Multi PertExtension.Series
open scoped BigOperators Classical ContDiff Topology Matrix.Norms.Frobenius
variable {V J I:Type} [DecidableEq V] [DecidableEq J] [Fintype V] [Fintype J] {R:Census V}
    {G: Gauge} {c f:Side} {π:Clip} {O:ChartRatio G} {P:PathData G} {S:StepData c f}

variable (K:Bulk.Kernel S π P O) (H:Forest S.ratio)(t:S.Choices)(x:Exterior.fieldDir G c 1)
    (δ:J→Multi.Hot R) (s:R.Mode) (χ: Bulk.Colors R G f)
set_option quotPrecheck false
local notation "X"=> Bulk.Joint S H (G:=G)
def smooth (G:Gauge) (F:Forest S.ratio) : Submodule ℝ (ℝ→ Config G f→ℂ) where
  carrier := {p | ContDiffAt ℝ ω (Bulk.posed S F p) 0}
  zero_mem' := (by change ContDiffAt ℝ ω (fun (_: Bulk.Joint S F (G:=G))=> (0:ℂ)) 0; exact contDiffAt_const)
  add_mem' := by
    intro x y hP hQ
    exact (show ContDiffAt ℝ ω (fun p=> Bulk.posed S F x p + Bulk.posed S F y p) 0 from ContDiffAt.add hP hQ)
  smul_mem' := fun d x hP => by
    have hP' : ContDiffAt ℝ ω (Bulk.posed S F x) 0 := hP
    exact hP'.const_smul (d:ℝ)

lemma smooth_iff (d: ℝ→ Config G f→ℂ) :
    d∈smooth G H ↔ ContDiffAt ℝ ω (Bulk.posed S H d) 0:= Iff.rfl

abbrev Driver (G:Gauge) (F:Forest S.ratio):= ↥(smooth G F)
local notation "Ω"=> Driver G H
abbrev room (Y:J→Driver G H) (v:J→ℂ) (s':Multi.Hot R) : ℝ→ Config G f→ℂ:=
  Exhibit.room δ v (fun j=> (Y j).val) s'
abbrev sheet (Y:J→Driver G H) (v:J→ℂ) : Bulk.Colors R G f:=
  Exhibit.sheets δ χ (fun j=> (Y j).val) v

abbrev publish (Y:J→Driver G H) (v:J→ℂ) (r i:ℕ):ℂ:=
  Symmetry.Orbit.words K H t (sheet H δ χ Y v) r s i x
variable (Y:J→Driver G H)
    (hδ:Exhibit.relevant δ s (Planet.pack univ))
    {r i:ℕ}(hr:i≤r)

local notation "Γ"=> fun j:J=> (δ j).val

omit [Fintype V] in
include hδ in
lemma unique_shape : Injective δ:= by
 have he:Fits (fun j:J=> (δ j).val) univ:= hδ.1
 intro a b h; by_contra hc
 have hl:Disjoint (δ a).val.val (δ b).val.val:= he.1 (mem_univ a) (mem_univ b) hc; rw [h] at hl; exact (δ b).prop.ne_empty (disjoint_self.mp hl)

omit [DecidableEq J] [Fintype V] in
lemma room_here (hu:Injective δ) (v:J→ℂ)(j:J) : room H δ Y v (δ j)= v j • (Y j).val:= by
 unfold room Exhibit.room; rw [Finset.sum_eq_single j]
 · exact fun i hi hv=> (hv (hu (mem_filter.mp hi).2)).elim
 simp
omit [DecidableEq J] [Fintype V] in
lemma room_blank (v:J→ℂ)(u:Multi.Hot R)(hu:u∉Set.range δ): room H δ Y v u=0:= by
 refine Finset.sum_eq_zero fun i hi=>?_; exact (hu ⟨i,(mem_filter.mp hi).2⟩).elim

include hδ hr
set_option maxHeartbeats 300000 in
lemma pitched (v:J→ℂ):
    publish K H t x δ s χ Y v r i= publish K H t x δ s χ Y 1 r i * ∏ i:J,v i:=by
 let p:= Planet.pack (univ:Finset J)
 let A:= Exhibit.circuit δ s
 have he(j:A):j.val=p:= Exhibit.shuffled δ p j.val (Finset.subset_univ _) hδ.1 (((mem_filter.mp j.prop).2.2).trans hδ.2.symm)
 have hs : Exhibit.circuit δ s={p}:=Finset.ext_iff.mpr fun a=>⟨fun hp=>mem_singleton.mpr (he ⟨a,hp⟩),fun hs=> (mem_singleton.mp hs).symm ▸ mem_filter.mpr ⟨mem_univ _,hδ⟩⟩
 have hx (z:J→ℂ): publish K H t x δ s χ Y z r i=Exhibit.wake (r:=r) (i:=i) δ χ (fun i=>(Y i).val) K H t x s p*(∏ i:J,z i):= by
    unfold publish sheet
    rw [Exhibit.switch δ χ (fun i=>(Y i).val) z K H t (fun i=>(smooth_iff H _).1 (Y i).prop) x s hr, hs, Finset.sum_singleton]
 rw [hx v,hx (1:J→ℂ)]; simp only [Pi.one_apply,Finset.prod_const_one,mul_one]

lemma tones (j:J)(F0:Ω)(a:ℝ) :
    publish K H t x δ s χ (Function.update Y j (a • F0)) 1 r i= a • publish K H t x δ s χ (Function.update Y j F0) 1 r i:= by
 let F:= Function.update Y j F0; let g:= Function.update Y j (a • F0)
 let v:= Function.update (1:J→ℂ) j (a:ℂ); have hc:∏ i:J,v i=(a:ℂ):= by
    rw [prod_eq_single j]; exact Function.update_self ..
    · intro i _ hi; exact Function.update_of_ne hi ..
    simp
 have h: sheet H δ χ g 1=sheet H δ χ F v:= by
    refine congrArg (fun q=> (⟨χ.vac,q,χ.power⟩: Colors R G f)) (show room H δ g 1=room H δ F v from ?_) -- F0 is not χ
    funext u; by_cases hu:u∈Set.range δ
    · obtain ⟨i,rfl⟩:= hu; rw [room_here H δ g (unique_shape δ s hδ), room_here H δ F (unique_shape δ s hδ),Pi.one_apply,one_smul]; by_cases hi:i=j
      · subst i; simp only [g,F,v,Function.update_self]; exact funext fun t=>funext fun U=>Complex.real_smul
      rw [show g i= Y i from Function.update_of_ne hi .., show F i=Y i from Function.update_of_ne hi .., show v i=1 from Function.update_of_ne hi .., one_smul]
    rw [room_blank H δ g _ _ hu,room_blank H δ F _ _ hu]
 change Symmetry.Orbit.words K H t (sheet H δ χ g 1) r s i x= a • publish K H t x δ s χ F 1 r i
 rw [h]
 change publish K H t x δ s χ F v r i= _
 rw [pitched K H t x δ s χ F hδ hr v,hc,Complex.real_smul]; exact mul_comm ..

section
-- Split one driver into two marked copies.
variable (j:J)
abbrev double : Option J → Multi.Hot R:= fun k=> Option.elim k (δ j) δ
local notation "γ"=> double δ j
local notation "D"=> fun v:Option J => (γ v).val
local notation "D0"=> (Exhibit.circuit γ s)
omit hr
omit [Fintype V] in
lemma branches (p:(Planet.Whole (Option J)).Mode) (hp: p∈ Exhibit.circuit (double δ j) s):
    none∈p.val ↔ some j∉p.val:= by
 obtain ⟨ha,H⟩:= (show Exhibit.relevant (double δ j) s p from (mem_filter.mp hp).2)
 obtain ⟨hc,W⟩:= (show Exhibit.relevant δ s (Planet.pack univ) from hδ)
 have hc' : Fits (fun j:J=> (δ j).val) univ:=hc
 unfold Translation.stamp at W H; rw [dif_pos ha] at H; rw [dif_pos hc] at W
 obtain ⟨a,ht⟩:=(δ j).prop
 have hv (hi: none∈p.val) (he: some j∈ p.val): False:= Finset.disjoint_left.mp (show Disjoint (D none).val (D (some j)).val from ha.1 hi he (by simp)) ht ht
 refine ⟨fun u v=> hv u v,fun hz=>?_⟩
 have hm:a∈(unionTag D p.val ha).val:= by
    rw [H,← W]
    exact mem_biUnion.mpr ⟨j,mem_univ _,ht⟩
 obtain ⟨k,hk,hn⟩:= (show ∃ k∈p.val,a∈(D k).val from mem_biUnion.mp hm)
 rcases k with _|k <;> [exact hk ; skip]
 exact (Finset.disjoint_left.mp (hc'.1 (mem_univ j) (mem_univ k) (show j ≠ k from fun h=> hz (h.symm ▸ hk))) ht (show a ∈(δ k).val.val from hn)).elim

-- a weight 1 or 0; combine first/second copy versions. Do not assume gauge price/interchange.
abbrev onPair (c d:ℝ) : Option J →ℂ:= fun k=> Option.elim k (c:ℂ) (Function.update (1:J→ℂ) j (d:ℂ))
abbrev halfA (a b:Ω) : Option J → Ω:= fun k=> Option.elim k a (Function.update Y j b)

local notation "hX"=> hδ
local notation "Z"=>onPair j
local notation "Γ₁"=> halfA H Y j
omit [Fintype V] in
lemma harness (a b:Ω) (c₀ c₁:ℝ):
    sheet H (double δ j) χ (halfA H Y j a b) (onPair j c₀ c₁)
      =sheet H δ χ (Function.update Y j (c₀ • a + c₁ • b)) 1:= by

 let v:= onPair j c₀ c₁; let F:=Γ₁ a b; let D' (t:Multi.Hot R):= room H γ F v t
 let U:= Function.update Y j (c₀ • a + c₁ • b); let T':= Function.update Y j b; let v':= Function.update (1:J→ℂ) j (c₁:ℂ)
 have he (t:Multi.Hot R): D' t=(if δ j=t then (c₀:ℂ) • a.val else 0) + room H δ T' v' t:= by
    unfold D' F room Exhibit.room; rw [Finset.sum_filter,Fintype.sum_option,Finset.sum_filter]; rfl
 refine congrArg (fun q=>(⟨χ.vac,q,χ.power⟩:Colors R G f)) (show D' = room H δ U 1 from ?_)
 funext i; rw [he]; by_cases h:i ∈ Set.range δ
 · obtain ⟨x,rfl⟩:=h; rw [room_here H δ _ (unique_shape δ s hδ),room_here H δ _ (unique_shape δ s hδ),Pi.one_apply,one_smul]
   by_cases ht:j=x; · subst x; rw [if_pos rfl, (show v' j=(c₁:ℂ) from Function.update_self ..), show T' j=b from Function.update_self .., show U j=c₀ • a + c₁ • b from Function.update_self ..]; exact funext fun i=>funext fun U=> by change (c₀:ℂ)*_+(c₁:ℂ)*_= (c₀:ℝ) • _+ (c₁:ℝ) • _; rw [Complex.real_smul,Complex.real_smul]
   rw [if_neg (fun H=>ht (unique_shape δ s hδ H)), show U x=Y x from Function.update_of_ne (Ne.symm ht) .., show T' x=Y x from Function.update_of_ne (Ne.symm ht) .., show v' x=1 from Function.update_of_ne (Ne.symm ht) .., zero_add,one_smul]
 rw [if_neg (fun H=> h ⟨j,H⟩),room_blank H δ _ _ _ h,room_blank H δ _ _ _ h,add_zero]

include hr
lemma doubling (a b:Ω) :
    publish K H t x δ s χ (Function.update Y j (a+b)) 1 r i=
      publish K H t x δ s χ (Function.update Y j a) 1 r i+ publish K H t x δ s χ (Function.update Y j b) 1 r i := by
 let M:= halfA H Y j a b; let f(v:(Planet.Whole (Option J)).Mode):ℂ:= Exhibit.wake (r:=r) (i:=i) γ χ (fun i=>(M i).val) K H t x s v
 have hv (c₀ c₁:ℝ): publish K H t x δ s χ (Function.update Y j (c₀ • a + c₁ • b)) 1 r i= ∑ v∈ D0, f v * (∏ i∈v.val,(onPair j c₀ c₁) i):= by unfold publish; rw [←harness H δ s χ Y hδ j a b]; exact Exhibit.switch γ χ (fun i=>_) _ K H t (fun k=>(smooth_iff H (M k).val).1 (M k).prop) x s hr
 have hp(p₀:(Planet.Whole (Option J)).Mode)(t₀: Option J):
       (∏ i∈p₀.val,(if i=t₀ then (0:ℂ) else 1))= if t₀∈p₀.val then 0 else 1:=by simp
 have hc (u:Option J):(Z 1 0) u=(if u= some j then 0 else 1):=by cases u with
    | none=> simp [onPair]
    | some u=> by_cases ht:u=j <;> simp [onPair,Option.elim,ht]
 have hd (u:Option J):(Z 0 1) u=(if u= none then 0 else 1):=by cases u with
    | none=> simp [onPair]
    | some u=> by_cases ht:u=j <;> simp [onPair,Option.elim,ht]
 have he (u:Option J):(Z 1 1) u=1:=by cases u with
    | none=> simp [onPair]
    | some u=> by_cases ht:u=j <;> simp [onPair,Option.elim,ht]
 have hg:=hv 0 1; have hf:=hv 1 0; have hk:=hv 1 1; simp only [zero_smul,zero_add,one_smul,add_zero] at hk hf hg
 rw [hk,hf,hg,←Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun u hu=>?_; simp_rw [he,hc,hd,hp,prod_const_one]; by_cases H: some j∈ u.val <;> simp [H,branches δ s hδ j u hu]
end
-- `DecidableEq J` diamonds: can't select one in shape; reduce update proofs to common one.
noncomputable def gesture (hδ:Exhibit.relevant δ s (Planet.pack univ)) (hr:i≤r) :
    MultilinearMap ℝ (fun _:J=>Driver G H) ℂ:= by
 let F (Y : J→Driver G H):= publish K H t x δ s χ Y 1 r i
 let d:= (inferInstance : DecidableEq J)
 refine ⟨F,?_,?_⟩
 · intro D Y j a b
   rw [Subsingleton.elim D d]; clear D
   exact doubling K H t x δ s χ Y hδ hr j a b
 intro D Y j T a
 rw [Subsingleton.elim D d]; clear D
 exact tones K H t x δ s χ Y hδ hr j a T

end YM.Qlocal.Harmony.Focal
