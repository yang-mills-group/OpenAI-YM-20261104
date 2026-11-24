import YM.Integration.WilsonThermometerWeakMeasuredBasis

/-! Linear combination in the original three-component transfer. The corrected
polynomial and its fitted coordinate use exactly the physical source enrolled at the root. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPhysicalCombination
open Function Filter Set MeasureTheory RG RG12 Extra.Histories Lattice Wilson Source Labels
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local GermGraph Next.Rank.Spindle Next.Rank Configuration Normal Rise
open Perch Glimmer LiftMark Beamer Station Atlas Tariffs MvPolynomial Ribbon
open WilsonThermometerWeakBasisCalibration WilsonThermometerOwnOffsetField
open scoped Classical Topology BigOperators
variable {G:Gauge} {n:Side} {d D b:ℕ}

def filed (F:Frame G d) {J:Type*} (W:F.Index→poly J) (u:F.Coeff) : poly J:=∑ i,u i•W i

theorem stock (F:Frame G d) (W:F.Index→poly (slotC G b)) {a:ℝ}
    (charge:∀ i,coin (W i)≤a) (degree:∀ i,(W i).totalDegree≤D) (spirit:∀ i,Spirit (W i))
    (u:F.Coeff):coin (filed F W u)≤a*F.coeffSize u ∧ (filed F W u).totalDegree≤D ∧ Spirit (filed F W u):=by
  refine ⟨?_,(totalDegree_finsetSum ..).trans (Finset.sup_le (fun i _=>(totalDegree_smul_le ..).trans (degree i))),?_⟩
  · apply (Rise.collect 0 zero_le_one ..).trans
    calc
      _ ≤ ∑ i,‖u i‖*a:=Finset.sum_le_sum fun i _=>(peak_cost 1 0 _ _ zero_le_one).trans (mul_le_mul_of_nonneg_left (charge i) (norm_nonneg _))
      _ = _:=by rw [← Finset.sum_mul,mul_comm];rfl
  · intro x t
    simp only [filed,text,map_sum,map_smul,smul_eq_mul];apply Finset.sum_congr rfl;intro i _;exact congrArg (fun z:ℂ=>u i*z) (spirit i x t)

def observed (v:Body) (U:Config G n):Tape G n→ₗ[ℂ]ℂ where
  toFun A:=(A v).2.1 U
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

variable (R:Run G) {k N p:ℕ}
local notation "Rf" => R.family
local notation "F" => R.family.labels.level d
local notation "P" => R.family.path.rep N p k
local notation "Lev" => R.family.path.levels

theorem assembled (u:(F).Coeff):chunk (C:=Rf) (primaryLetter d) u=∑ i,u i•input R d i:=by
  funext l
  by_cases h:l=primaryLetter d
  · subst l;simp only [Finset.sum_apply,Pi.smul_apply,input,chunk_self]
    funext j; rw [Finset.sum_apply,Finset.sum_eq_single j]
    · change u j=u j*((Pi.single j 1:(F).Coeff) j);rw [Pi.single_eq_same,mul_one]
    · intro i _ h;change u i*((Pi.single i 1:(F).Coeff) j)=0;rw [Pi.single_eq_of_ne h.symm,mul_zero]
    · simp
  · simp only [input,Finset.sum_apply,Pi.smul_apply,chunk_miss _ h,smul_zero,Finset.sum_const_zero]

theorem tested (V:Sight Rf d p) (g:ℝ) {δ:ℝ} (W:(F).Index→poly (slotC G b))
    (X:(F).Index→ Coefficient F ((Rf).side k p))
    (record:∀ i,V k (input R d i) (line (primaryLetter d))=invoice (X i) 0 ((Rf).localSection d) (P))
    (fit:∀ i U,Healthy (tau (Lev) k) (Spindle.patch b 0) U →
       ‖(X i).exponentialEntry 0 ((Rf).localSection d) (P) U-signet 0 g (W i) U‖≤δ)
    (u:(F).Coeff) (Y:Coefficient F ((Rf).side k p))
    (actual:V k (chunk (primaryLetter d) u) (line (primaryLetter d))=invoice Y 0 ((Rf).localSection d) (P)) :
    ∀ U,Healthy (tau (Lev) k) (Spindle.patch b 0) U →
      ‖Y.exponentialEntry 0 ((Rf).localSection d) (P) U-signet 0 g (filed F W u) U‖≤δ*(F).coeffSize u:=by
  intro U health
  let read:=observed (G:=G) (line (primaryLetter d)) U
  have valued: Y.exponentialEntry 0 ((Rf).localSection d) (P) U= ∑ i,u i*(X i).exponentialEntry 0 ((Rf).localSection d) (P) U:=by
    change (invoice Y 0 ((Rf).localSection d) (P)).2.1 U=_
    rw [←actual];change read (V k (chunk (primaryLetter d) u))=_
    rw [assembled R u,map_sum,map_sum]
    apply Finset.sum_congr rfl;intro i _;rw [map_smul,map_smul];change u i*((V k (input R d i) _).2.1 U)=_;rw [record]
    rfl
  rw [valued,show signet 0 g (filed F W u) U=∑ i,u i*signet 0 g (W i) U by simp [Spindle.signet,filed,text]]
  rw [←Finset.sum_sub_distrib]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ i,‖u i‖*δ:=Finset.sum_le_sum (fun i _=>by rw [←mul_sub,norm_mul];exact mul_le_mul_of_nonneg_left (fit i U health) (norm_nonneg _))
    _ = _:=by rw [←Finset.sum_mul,mul_comm];rfl

private def wick (wide:4*b≤wood (Lev) k) (E:AtlasData G (Rf).S p) :
    poly (slotC G b)→ₗ[ℂ]poly (KeyIn G d) where
  toFun:=WilsonThermometerWeakGroupCoordinate.contracted R d wide E
  map_add' _ _:=by simp only [WilsonThermometerWeakGroupCoordinate.contracted,map_add,LiftMark.trim_add]
  map_smul' _ _:=by simp only [WilsonThermometerWeakGroupCoordinate.contracted,map_smul,LiftMark.trim_smul,RingHom.id_apply]

theorem calibrated (wide:4*b≤wood (Lev) k) (E:AtlasData G (Rf).S p) (W:(F).Index→poly (slotC G b))
    (T:(F).Coeff≃ₗ[ℂ](F).Coeff) (cost:∀ u,(F).coeffSize (T.symm u)≤2*(F).coeffSize u)
    {h:ℝ} (hh:h≠0) (K:∀ i,∃ z:(F).Coeff,(F).scaled h z=T (Size.axis F i) ∧
      expose F z=WilsonThermometerWeakGroupCoordinate.contracted R d wide E (W i)) (x:(F).Coeff):
    let u:=T.symm ((F).scaled h x)
    (F).coeffSize u≤2*(F).coeffSize ((F).scaled h x) ∧
      WilsonThermometerWeakGroupCoordinate.contracted R d wide E (filed F W u)=expose F x:=by
  intro u;refine ⟨cost _,?_⟩
  choose z scal see using K
  let a:(F).Coeff:=∑ i,u i•z i
  have image:(F).scaled h a=(F).scaled h x:=by
    dsimp only [a];rw [map_sum]
    calc
      _ = ∑ i,T (u i•Size.axis F i):=Finset.sum_congr rfl fun i _=>by rw [map_smul,scal,map_smul]
      _ = T (∑ i,u i•Size.axis F i):=(map_sum T _ _).symm
      _ = _:=by rw [Size.sum_axes];exact T.apply_symm_apply _
  have same:a=x:=by
    have eq:=congrArg ((F).scaled h⁻¹) image
    have cancel (v:(F).Coeff):(F).scaled h⁻¹ ((F).scaled h v)=v:=by
      have inv:=(F).scaled_inv (inv_ne_zero hh) v
      rwa [inv_inv] at inv
    exact (cancel a).symm.trans (eq.trans (cancel x))
  rw [←same];change wick (d:=d) R wide E (∑ i,u i•W i)=expose F (∑ i,u i•z i)
  simp only [map_sum,map_smul];apply Finset.sum_congr rfl;intro i _
  exact congrArg (fun z=>u i•z) (see i).symm

end YM.Integration.WilsonThermometerWeakPhysicalCombination
end
