import YM.Integration.WilsonAddressedWeakNativePolynomials

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakEnrollment
open Function Lattice Wilson RG Next.Rank Cells MeasureTheory Next.Rank.Tapes Next.Rank.Tapes.West
open Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station
open Ac Alarm Thirst Corona Value Finset Edition Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} {C:Family G} {k N p n u:ℕ} {ξ:Purse} {Ψ:AtlasData G C.S p}
  {R:Lead G C.S p} {P:(i:ℕ)→Rep G (C.side i p)} {c:Course C N p k}
local notation "Lev" => C.path.levels
section
variable {n : Side} {V ι κ : Type} [Fintype V] [DecidableEq V]
private lemma basicLight {ζ : V→ Site n} [Fintype ι] [Fintype κ] {r R : V→ℝ} {h k e₀ : ℝ} (L : Rep G n) {A : ι→ SourceAt G ζ} {K : κ→ Lifted G ζ L.p.threshold} (H : Unpacks A L.p r e₀ h) (ht : prepared (q:=L.p) K r e₀ k) (hp : ∀ i,0≤ R i) (hr : R ≤ r): Light L A K R e₀ h k:= by
  have ht' (s:modes V): Poly.toll R s ≤ Poly.toll r s:= Finset.prod_le_prod (fun i _=> hp i) (fun i _=> hr i)
  obtain ⟨m,hm,h⟩:=H; obtain ⟨p,hp,hk⟩:=ht; constructor
  · refine ⟨fun i=>m i*Value.charge L.p e₀ (A i).extent, fun i=>⟨mul_nonneg (hm i|>.1) (Real.exp_pos _).le,fun U hx=>?_⟩, fun i=>?_⟩
    · refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ht' _) (Real.exp_pos _).le) (norm_nonneg _)) ?_; rw [mul_assoc]; apply (mul_le_mul_of_nonneg_left (((transferD ..).mp (hm i)).2 _ hx) (Real.exp_pos _).le).trans_eq (mul_comm ..)
    simpa [Value.charge] using! (sum_pay _ _ _ (fun i=>mul_nonneg (hm i|>.1) (Real.exp_pos _).le)).1 (h i)
  refine ⟨fun i=>p i*Value.charge L.p e₀ (K i).extent, fun i=>⟨mul_nonneg (hp i|>.1) (Real.exp_pos _).le,fun U=>?_⟩,fun i=>?_⟩
  · refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ht' _) (Real.exp_pos _).le) (norm_nonneg _)) ?_; rw [mul_assoc]; exact (mul_le_mul_of_nonneg_left ((hp i).2 U) (Real.exp_pos _).le).trans_eq (mul_comm ..)
  simpa [Value.charge] using! (sum_pay _ _ _ (fun i=> mul_nonneg (hp i|>.1) (Real.exp_pos _).le)).1 (hk i)

end
theorem original (x:Points n) (wide:4*sizeQ C k≤wood (Lev) k)
    (raw:Config G (C.side N p)→veil ((Ship.yard C ξ.band c.allow p).Cell × Fin n))
    (W:Fin n→poly (slotC G (sizeQ C k))) (price:∀ i,coin (W i)≤ξ.principal (clim (Lev) k))
    (deg:∀ i,totalDegree (W i)≤ξ.taylor) (spin:∀ i,Spirit (W i))
    (gift:Ceremony ξ c P R Ψ) (fare:Caff (G:=G) ξ (clim (Lev) k) (k-middle (Lev) ξ.band k) u n)
    (hu:2≤u) (fit:Fit (Lev) ξ.band k x) (crew:Plessey ξ x c P R u)
    {ι κ:Type} [Fintype ι] [Fintype κ]
    (file:Listens C ξ.band (v:=n) c.allow p→SourceAt G (seats C ξ.band x c.allow p))
    (H:ι→SourceAt G (seats C ξ.band x c.allow p)) (K:κ→Lifted G (seats C ξ.band x c.allow p) (P k).p.threshold)
    (posted:∀ i,(file i).extent=swath ((Ship.yard C ξ.band c.allow p).omega i.1) (seats C ξ.band x c.allow p i)
          (halo (ξ.era.coast.Q*(P k).p.B) ({0}:Support (C.side k p))) ∧
        (file i).fires=Glyph.slot i ∧ (file i).value=
          dot ((Ship.yard C ξ.band c.allow p).hand i.1) ∘ signet 0 (LiftMark.GaugeScale C k N p) (W i.2) ∘
            pull ((Ship.yard C ξ.band c.allow p).omega i.1) (seats C ξ.band x c.allow p i))
    (same:c.flow raw k c.allow=dust (P k) (Sum.elim H file) K) (quiet:Background (P k) K)
    (reg:Unpacks H (P k).p (fun _=>Perch.bill ξ.f (clim (Lev) k)) (load ξ.era) (Perch.bill (-(ξ.goal:ℝ)) (clim (Lev) k)))
    (hard:Alarm.prepared (q:=(P k).p) K (fun _=>Perch.bill ξ.f (clim (Lev) k)) (load ξ.era) (Real.exp (-(Paint.trib ξ.era.coast.a (clim (Lev) k))))):
    Chast P c Ψ x (fun j=>lifted Ψ (W j) (Station.choose (Lev) ξ.band k x j) k wide) ξ u raw:=by
  let Y:=fun j=>lifted Ψ (W j) (Station.choose (Lev) ξ.band k x j) k wide
  have filed:Kith (A:=C.path.levels) Y x ξ:=WilsonAddressedWeakNativePolynomials.fitted x wide W price deg spin
  apply legion gift filed fare hu fit crew
  let F:=tapestry filed fare le_rfl (before (Lev) ξ.band k) gift.sens c
  let α:=Listens C ξ.band (v:=n) c.allow p
  let β:=Bale C k ξ.band p ξ.horizon x le_rfl
  let leaf:α→β:=fun t=>⟨t.1,solitaire x t.2 ξ p k (Lev)⟩
  have hQ:(P k).p.B=walls (clim (Lev) k):=(gift.birth k (before ..) le_rfl).1
  unfold leased; dsimp only
  refine ⟨ι,κ,inferInstance,inferInstance,H,K,same.trans ?_,quiet,?_⟩
  rotate_left
  · rw [Nat.sub_self,Purse.epoch,pow_zero,one_mul]
    rw [show Perch.gas ξ.era.coast (clim (Lev) k)=Real.exp (-Paint.trib ξ.era.coast.a (clim (Lev) k)) by unfold Perch.gas Paint.trib;ring_nf]
    exact basicLight (P k) reg hard (fun i=>(Real.exp_pos _).le) (fun i=>Glimmer.billed _ (cash_le _ _ hu))
  ext1 U;unfold dust;rw [Fintype.sum_sum_type,Fintype.sum_sum_type];congr 3
  let b:=(P k).p.threshold
  have he (t:α):(F (leaf t)).amount b U=(file t).amount b U:=by
    let z:=(solitaire x t.2 ξ p k (Lev)).val
    have hx:(F (leaf t)).extent=(file t).extent:=by
      rw [(posted t).1]
      change Spindle.patch (ξ.era.coast.Q*walls (clim (Lev) k))
        (readers (C:=C) (b:=ξ.band) x c.allow c.allow (t.1,Head z))=_
      rw [swath_iffHalo,x_head x t.2 (C:=C),hQ]
      simp only [swath,image_singleton,affine,Signed.act_zero,zero_add];rfl
    have ht:(F (leaf t)).fires=(file t).fires:=by
      rw [(posted t).2.1]; apply Subtype.ext
      change {t.1} ×ˢ ({t.2}: Finset _)={t}
      rw [singleton_product_singleton]
    have hv:(F (leaf t)).value=(file t).value:=by
      rw [(posted t).2.2]
      funext Z
      change gloryFt (C:=C) x ξ.band p c.allow le_rfl (before ..) t.1 z
        (anneals C c k) (vista R Y le_rfl z.val) Z=_
      rw [bootwarm C c c.allow]
      exact WilsonAddressedWeakNativePolynomials.singleton x wide W gift t.1 t.2 _ _
    rw [SourceAt.amount,SourceAt.amount,hx,ht,hv]
  apply congr_arg ((∑ i,(H i).amount b U)+·)
  change (∑ i,(file i).amount b U)=∑ i,(F i).amount b U
  let V:=(univ (α:=α)).image leaf
  have injective:Injective leaf:=fun i j h=>by
    refine Prod.ext (show (leaf i).1=(leaf j).1 from congrArg Prod.fst h) ?_
    exact Finset.singleton_injective (congrArg (fun x:β=>x.2.val.val.val) h)
  rw [←sum_subset (subset_univ V) ?_,sum_image injective.injOn];simp_rw [he];try rfl
  intro i _ hi
  let Q:=i.2.val.val
  have hq:2≤Q.val.card:=by
    have hcard:0<Q.val.card:=Finset.card_pos.mpr i.2.val.property
    by_contra! hz
    obtain ⟨j,hj⟩:=Finset.card_eq_one.mp (show Q.val.card=1 by omega)
    have e:leaf (i.1,j)=i:=Prod.ext rfl (Subtype.ext (Subtype.ext (Subtype.ext hj.symm)))
    exact hi (mem_image.mpr ⟨_,mem_univ _,e⟩)
  change Poly.send (F i).fires (masked b (F i).extent (F i).value U)=_
  by_cases hz:Healthy b (F i).extent U
  · rw [masked_eq b _ _ _ hz]
    have h:vista R Y le_rfl Q=0:=strophe (C:=C) Y Q hq
    unfold Q at h
    simp only [F,tapestry,mimicFt,gloryFt,h,caseW,Function.comp_apply,text,map_zero,Edition.dot_zero,Poly.send_zero]
  rw [masked_ne _ _ _ _ hz,Poly.send_zero]
end YM.Integration.WilsonAddressedWeakEnrollment
end
