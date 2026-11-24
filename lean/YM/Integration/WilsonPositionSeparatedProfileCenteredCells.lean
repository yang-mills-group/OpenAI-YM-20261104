import YM.RG05Readout.Pulse.Excursion

/-! Normalized subdivision of the original centered native test cell into
its actual block children, before applying a signed common profile. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileCenteredCells
open Function Set Finset MeasureTheory Lattice Wilson RG RG05Readout Address Native Pulse Flatten
open scoped Classical Topology BigOperators Pointwise
variable {G:Gauge} (C:Family G) (p n:ℕ)
local notation "H" => Bud C p n
local notation "L" => ((C.S.block n).val:ℝ)

def ray (i:H) (x:E4):E4:=displacement C p n i+L⁻¹ • x

private def tile (i:H):Set E4:=ray C p n i '' halfC

private theorem caught (i:H) (x:E4) (hx:x∈halfC) (a:Axis):⌊L*(ray C p n i x a)+1/2⌋=lift i a:=by
  have pos:0<L:=by exact_mod_cast (C.S.block n).pos
  have eq:L*(ray C p n i x a)=(lift i a:ℝ)+x a:=by
    change L*(L⁻¹*(lift i a:ℝ)+L⁻¹*(x a))=_
    rw [←mul_add,←mul_assoc,mul_inv_cancel₀ pos.ne',one_mul]
  rw [eq];apply Int.floor_eq_iff.mpr;obtain ⟨u,v⟩:=hx a;constructor <;> linarith

private theorem separate:Pairwise (Disjoint on tile C p n):=by
  intro i j ne;apply Set.disjoint_left.mpr;intro z zi zj
  obtain ⟨x,hx,rx⟩:=zi;obtain ⟨y,hy,ry⟩:=zj
  have same:lift i=lift j:=by funext a;rw [←caught C p n i x hx a,←caught C p n j y hy a,rx,ry]
  exact ne ((wrap_lift i).symm.trans ((congrArg (Lattice.wrap _) same).trans (wrap_lift j)))

private theorem within (i:H):tile C p n i⊆Native.box:=by
  rintro _ ⟨x,hx,rfl⟩;apply dist_box C p n i
  exact fun a=>abs_le.mpr ⟨(hx a).1,(hx a).2.le⟩

private theorem chart (i:H):MeasurableSet (tile C p n i):=by
  have pos:0<L:=by exact_mod_cast (C.S.block n).pos
  let h:=Homeomorph.smul (α:=E4) (Units.mk0 L⁻¹ (inv_ne_zero pos.ne'))
  let u:=Homeomorph.addLeft (displacement C p n i)
  have eq:ray C p n i=h.trans u:=rfl
  rw [tile,eq];exact (h.trans u).measurableEmbedding.measurableSet_image.mpr halft

private theorem single (i:H) (f:E4→ℂ):
    (∫x in tile C p n i,f x)=(Fintype.card H:ℂ)⁻¹*∫x in Native.box,f (ray C p n i x):=by
  have l:0<L:=by exact_mod_cast (C.S.block n).pos
  let h:=fun x:E4=>displacement C p n i+x
  rw [show tile C p n i=h '' (L⁻¹ • halfC) from Set.image_comp ..]
  rw [(measurePreserving_add_left volume (displacement C p n i)).setIntegral_image_emb ((Homeomorph.addLeft _).measurableEmbedding)]
  let f':=f ∘ h
  have bill:=Measure.setIntegral_comp_smul_of_pos (volume (α:=E4)) f' halfC (inv_pos.mpr l)
  rw [show Module.finrank ℝ E4=4 from by simp [E4],Measure.restrict_congr_set half_AE] at bill
  change (∫x in L⁻¹ • halfC,f' x)=_
  have use:(∫x in L⁻¹ • halfC,f' x)=(L⁻¹)^4 • ∫x in Native.box,f' (L⁻¹ • x):=by
    rw [bill,smul_smul,mul_inv_cancel₀ (pow_ne_zero _ (inv_ne_zero l.ne')),one_smul]
  rw [use,Complex.real_smul]
  have card:(Fintype.card H:ℂ)=((C.S.block n).val:ℂ)^4:=by rw [site_card];push_cast;rfl
  rw [card,Complex.ofReal_pow,Complex.ofReal_inv,inv_pow];rfl

private theorem assembled (f:E4→ℂ) (c:Continuous f):
    (∫x in ⋃i:H,tile C p n i,f x)=(Fintype.card H:ℂ)⁻¹*∑i:H,∫x in Native.box,f (ray C p n i x):=by
  rw [integral_iUnion_fintype (chart C p n) (separate C p n) (fun i=>(c.continuousOn.integrableOn_compact Pert.Cellular.cells_compact).mono_set (within C p n i))]
  simp_rw [single];rw [Finset.mul_sum]

/-- The child rays partition the parent up to its true boundary null set.
The proof uses the genuine Haar volume and the exact number of child sites. -/
theorem partition: (⋃i:H,tile C p n i)=ᵐ[volume] Native.box:=by
  let E:=⋃i:H,tile C p n i
  have inside:E⊆Native.box:=iUnion_subset (within C p n)
  have paid:=assembled C p n (fun _=>1) continuous_const
  have nz:(Fintype.card H:ℂ)≠0:=Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [setIntegral_const,Complex.real_smul,mul_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←mul_assoc,inv_mul_cancel₀ nz,one_mul] at paid
  have eq:volume.real E=volume.real Native.box:=Complex.ofReal_inj.mp paid
  have finite:volume Native.box≠⊤:=Pert.Cellular.cells_compact.measure_lt_top.ne
  have fm:volume E≠⊤:=((measure_mono inside).trans_lt Pert.Cellular.cells_compact.measure_lt_top).ne
  have size:volume E=volume Native.box:=(ENNReal.toReal_eq_toReal_iff' fm finite).mp eq
  exact ae_eq_of_ae_subset_of_measure_ge (ae_of_all _ inside) size.ge (MeasurableSet.iUnion (chart C p n)).nullMeasurableSet finite

theorem original (f:E4→ℂ) (c:Continuous f):
    (Fintype.card H:ℂ)⁻¹*(∑i:H,∫x in Native.box,f (ray C p n i x))=∫x in Native.box,f x:=by
  rw [←assembled C p n f c,Measure.restrict_congr_set (partition C p n)]

/-- Every genuine child has its actual centered displacement on the torus. -/
theorem child_place (i:H): C.S.place (child C p n i)=C.S.a n • displacement C p n i:=by
  let R:Ratio (C.side n p) (C.side (n+1) p):=(C.path.levels.clock.op n p).ratio
  have d:R.count.val≤(C.side (n+1) p).val:=by
    rw [R.exact_size];exact Nat.le_mul_of_pos_left _ (C.side n p).pos
  have di:(R.count.val:ℤ)≤(C.side (n+1) p).val:=by exact_mod_cast d
  have liftChild: lift (child C p n i)=lift i:=by
    apply lift_eq_iff.mpr
    constructor
    · have root:R.embed 0=0:=R.root.map_zero
      change R.embed 0+Lattice.wrap _ (lift i)=_;rw [root,zero_add]
    · intro a
      have mid:=lift_centers i a
      exact ⟨lt_of_le_of_lt (neg_le_neg di) mid.1,mid.2.trans di⟩
  unfold Schedule.place;rw [liftChild]
  apply PiLp.ext;intro a
  change C.S.a (n+1)*(lift i a:ℝ)=C.S.a n*(L⁻¹*(lift i a:ℝ))
  rw [C.S.a_step,div_eq_mul_inv,mul_assoc]

theorem child_voyager (i:H) (z:E4):voyager C p (n+1) (child C p n i) z=C.S.a n • ray C p n i z:=by
  unfold voyager ray;rw [child_place,C.S.a_step,smul_add,smul_smul,div_eq_mul_inv]

end YM.Integration.WilsonPositionSeparatedProfileCenteredCells
