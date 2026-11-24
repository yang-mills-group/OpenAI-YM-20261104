import YM.RG05Readout.Flatten.Amass
/-! Integrate true physical center on rooted cells. Uses volume on
 actual E4. No smoothness in center needed for descendants beyond stated
 Apollo.Gate norms.AE boundaries. Undifferentiated backgrounds.Unmasked.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Flatten
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station
open Records Basket Shadow
open scoped Pointwise Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}{I J V:Type}[DecidableEq V][Fintype V]
    {j b k D:ℕ}
set_option quotPrecheck false
local notation "A"=> C.S.a
local notation "Λ"=> C.S.toDepth
local notation "X!"=> C.side N p
local notation "Y!"=> C.side b p
local notation "G!"=>C.S.gridPoint
local notation "o!"=> C.S.place
local notation "ρ₀"=>C.S.radius p
open GridApprox
section mass
abbrev voyager (C:Family G)(p b:ℕ)(x:Site (C.side b p))(t:E4): E4:= C.S.place x + C.S.a b • t
def halfC:Set E4:= {u|∀ i:Axis, -(1/2:ℝ) ≤ u i ∧ u i < 1/2}
local notation "D!"=> halfC
lemma halft : MeasurableSet D!:=by
    rw [show D!=⋂ i:Axis,{x:E4| x i ∈ Set.Ico (-(1/2:ℝ)) (1/2)} from by ext x; rw [mem_iInter]; rfl]; apply MeasurableSet.iInter; intro i; apply measurableSet_Ico.preimage (show Measurable (fun x:E4=>x i) from by fun_prop)
lemma half_AE : D!=ᵐ[volume] Native.box:=by
   filter_upwards [Pert.Cellular.cell_AE] with x hx
   apply propext; constructor
   · intro h i; exact abs_le.mpr ⟨(h i).1,(h i).2.le⟩
   intro h i; exact ⟨(abs_le.mp (h i)).1,(abs_le.mp (h i)).2.lt_of_ne (hx i).2⟩
abbrev TravelS (y:Site Y!):= (fun x=> voyager C p b y x) '' D!
lemma wayVolume (y:Site Y!) : MeasurableSet (TravelS (C:=C) (b:=b) (p:=p) y):=by
   unfold TravelS; let r:=Homeomorph.smul (α:=E4) (Units.mk0 (A b) (C.S.a_pos _).ne'); let u:=Homeomorph.addLeft (o! y); have h:(fun x=>voyager C p b y x)=(r.trans u):=rfl; rw [h]; exact ((r.trans u).measurableEmbedding).measurableSet_image.mpr halft
-- exact powers from Haar. No losses.
lemma wayIntegral (y:Site Y!)(f:E4→ℂ): (∫ x in TravelS (C:=C) (b:=b) (p:=p) y,f x)=(A b)^4 • ∫ x in Native.box,f (voyager C p b y x):=by
    let u:=fun x:E4=>o! y+x
    rw [show TravelS (C:=C) (b:=b) (p:=p) y=u '' (A b • D!) from Set.image_comp ..]; rw [(measurePreserving_add_left volume (o! y)).setIntegral_image_emb ((Homeomorph.addLeft (o! y)).measurableEmbedding)]
    let f':=f ∘ u
    have hi:= Measure.setIntegral_comp_smul_of_pos (volume (α:=E4)) f' D! (C.S.a_pos b); rw [show Module.finrank ℝ E4=4 from by simp [E4],Measure.restrict_congr_set half_AE] at hi
    change (∫ x in A b • D!,f' x)=(A b)^4 • ∫ x in Native.box,f' (A b • x); rw [hi,smul_smul,mul_inv_cancel₀ (pow_ne_zero _ (C.S.a_pos _).ne'),one_smul]
private lemma side_x {z:Cover}{t:E4}(he:t∈D!) (x) (hx:x= G! b z+A b • t) (j:Axis): ⌊(x j)/(A b)+1/2⌋=z j:=by
   rw [hx,PiLp.add_apply,PiLp.smul_apply]; change ⌊(A b*(z j:ℝ) + (A b)* (t j))/(A b)+1/2⌋=_; rw [← mul_add, mul_div_cancel_left₀ _ (C.S.a_pos _).ne']
   obtain ⟨ht,hv⟩:=he j; apply Int.floor_eq_iff.mpr; constructor <;> linarith
lemma oneNode (x:E4){y z:Site Y!}(hx:x∈ TravelS (C:=C) (b:=b) (p:=p) y)(hy:x∈ TravelS (C:=C) (b:=b) (p:=p) z): y=z:=by
   obtain ⟨a,hx,h₁⟩:=hx; obtain ⟨a',hy,h₂⟩:=hy; have h:lift y= lift z:= funext fun j=> (side_x (C:=C) (b:=b) hx _ h₁.symm j).symm.trans (side_x (C:=C) (b:=b) hy _ h₂.symm _); nth_rw 1 [←wrap_lift y]; rw [h,wrap_lift]
lemma voyage {R:ℝ} (h:R+A b <ρ₀)(x:E4)(hp:‖x‖≤R):∃ y:Site Y!, x∈TravelS (C:=C) (b:=b) (p:=p) y:=by
   let z:Cover:=fun i=>⌊(x i)/(A b)+ 1/2⌋
   let t:E4:= WithLp.toLp 2 fun i=> x i/(A b)-(z i:ℝ)
   have he:x= G! b z+A b • t:=by apply PiLp.ext; intro i; change x i=(A b)*(z i:ℝ)+(A b)*(x i/(A b)-(z i:ℝ)); field_simp [(C.S.a_pos _).ne']; ring
   have ha:t∈ D!:=by
      intro i; have hv:=Int.floor_eq_iff.mp (rfl: ⌊(x i)/(A b)+1/2⌋= z i); change _≤ x i/(A b)- _ ∧ x i/(A b)- _ < _; constructor <;> linarith only [hv.1,hv.2]
   have ht: ‖A b • t‖≤ A b:=by rw [norm_smul,Real.norm_of_nonneg (C.S.a_pos _).le]; exact mul_le_of_le_one_right (C.S.a_pos _).le (Pert.Cellular.cells_bd (fun i=>abs_le.mpr ⟨(ha i).1,(ha i).2.le⟩))
   let y:=Lattice.wrap Y! z
   have hu: lift y=z:=reads_grid (u:=y) rfl ((norm_le_insert (G! b z) (A b • t)).trans_lt (lt_of_le_of_lt (add_le_add (he ▸ hp) ht) h)); refine ⟨y,t,ha,?_⟩; unfold voyager Schedule.place; rw [hu]; exact he.symm
section pulse
variable {R:ℝ}(f:E4→ℂ)(h:Continuous f)(hf:∀ x∈support f,‖x‖≤R)(hR:R+C.S.a b < C.S.radius p)
include h hf hR
lemma coverings : Integrable f ∧ (∫ x,f x)= ∑ y:Site Y!, (A b)^4 • ∫ x in Native.box,f (voyager C p b y x) :=by
   let T y:= TravelS (C:=C) (b:=b) (p:=p) y; let z y:= (T y).indicator f
   have he:f=fun x=>∑ y:Site Y!,z y x:=by
      funext x; by_cases hp:x∈support f
      · obtain ⟨y,hp⟩:= voyage hR x (hf x hp); rw [Finset.sum_eq_single y]; exact (indicator_of_mem hp _).symm
        · intro i _ H; exact indicator_of_notMem (fun h₀=> H (oneNode (C:=C) (b:=b) (p:=p) x h₀ hp)) _
        simp
      have h':f x=0:=notMem_support.mp hp; calc
         _=0:=h'
         _=_:= (sum_eq_zero fun i _=> by unfold z; rw [Set.indicator]; split; exact h'; rfl).symm
   have hi (i:Site Y!) : Integrable (z i):=by
        let K:= (fun x=>voyager C p b i x) '' Native.box; have hz:IsCompact K:= Pert.Cellular.cells_compact.image (by unfold voyager; fun_prop); exact (integrable_indicator_iff (wayVolume (C:=C) (p:=p) (b:=b) i)).2 ((h.continuousOn.integrableOn_compact hz).mono_set (image_mono fun x hx j=>abs_le.mpr ⟨(hx j).1,(hx j).2.le⟩))
   refine ⟨he.symm ▸ (show Integrable (fun x=>∑ y:Site Y!, z y x) from ?_),?_⟩
   · exact (by simpa only [← Finset.sum_apply] using (integrable_finsetSum Finset.univ fun i _=>hi i))
   conv_lhs => rw [he]; arg 2
   rw [integral_finsetSum Finset.univ (fun i _=> hi i)]; apply sum_congr rfl; intro i _; unfold z; rw [integral_indicator (s:=T i) (wayVolume i)]; exact wayIntegral i f -- implicit
omit hf hR
noncomputable def voicePulse (h:ContinuousOn f Native.box):PulseC where
    toFun a:=∫ x in Native.box,a.val x*f x
    map_add' a b:=by
       simp_rw [show ((a+b).val)=a.val+b.val from rfl,Pi.add_apply,add_mul]; exact integral_add (((body_smooth a 1|>.continuous.continuousOn).mul h).integrableOn_compact Pert.Cellular.cells_compact) (((body_smooth b 1|>.continuous.continuousOn).mul h).integrableOn_compact Pert.Cellular.cells_compact)
    map_smul' c a:=by
       change (∫ x in Native.box,(c*a.val x)* f x)= c*(∫ x in Native.box,a.val x*f x); simp_rw [mul_assoc, integral_const_mul]
omit h
lemma voice_cost (h:ContinuousOn f Native.box){b:ℝ} (hv:∀ x∈ Native.box, ‖f x‖≤b)(d:ℕ):Priced d (voicePulse f h) (volume.real Native.box*b):=by
   intro x s hx; unfold voicePulse; change ‖(∫ y in Native.box,x.val y*f y)‖ ≤ _
   have ht z(hz:z∈Native.box) : ‖x.val z*f z‖≤ s*b:=by let v:=hx 0 (Nat.zero_le _) z hz; rw [norm_iteratedFDeriv_zero] at v; rw [norm_mul]; exact mul_le_mul v (hv z hz) (norm_nonneg _) hx.nonneg
   exact le_trans (norm_setIntegral_le_of_norm_le_const Pert.Cellular.cells_compact.measure_lt_top ht) (by exact le_of_eq (by ring))
end pulse
end mass
end YM.RG05Readout.Flatten
