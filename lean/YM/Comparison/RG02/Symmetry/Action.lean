import YM.Comparison.RG02.Symmetry.Tariff
/-!
# Constant-in-block gauge at each bandwidth on the step slice

Use all sites at once; *no* sum or expectation over gauges. No indicator/halo remapping for
purported curvature norm. Window (indicator may depend on t) exact integral statements.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Symmetry
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested YM.Push.SectorMeasure
open Marker Multi Order YM.Next.SectorChange Integral Actual Laplace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio) (w : S.Choices)
local notation "X"=> Site c→G.El
local notation "Y"=> F.Slice G
variable (d : Site c→ G.El)
local notation "ν"=> F.order G
namespace Switch
def k (S : StepData c f) := d ∘ S.ratio.parent
private def L (S:StepData c f) (i:Edge (Site f)):= k d S i.1
private def R (S:StepData c f) (i:Edge (Site f)):= (k d S (i.1+step i.2))⁻¹

def move : F.Slice G≃ₜ F.Slice G where
 toFun y j := L d S j * y j*R d S j
 invFun y j := (L d S j)⁻¹ * y j*(R d S j)⁻¹
 left_inv y := by funext j; group
 right_inv y := by funext j; group
 continuous_toFun := continuous_pi fun i=> ((continuous_const (y:=L d S i)).mul (continuous_apply (A:= fun _ : F.Free => G.El) i)).mul (continuous_const (y:=R d S i))
 continuous_invFun := continuous_pi fun i=> ((continuous_const (y:=(L d S i)⁻¹)).mul (continuous_apply (A:= fun _ : F.Free=> G.El) i)).mul (continuous_const (y:=(R d S i)⁻¹))
lemma preserves : MeasurePreserving (move F d) ν ν:= measurePreserving_pi _ _ fun i:F.Free=> G.preserve_two_sided (L d S i) (R d S i)
lemma cont : Continuous (fun z:X×Y=>move F z.1 z.2):= continuous_pi fun i=> by
   change Continuous (fun z:X×Y=> L z.1 S i * z.2 i * R z.1 S i)
   unfold L R k; simp only [Function.comp_apply]; fun_prop
lemma behind : Continuous (fun z:X × Y=> (move F z.1).symm z.2) := continuous_pi fun i=> by
   change Continuous (fun z:X×Y=> (L z.1 S i)⁻¹ * z.2 i * (R z.1 S i)⁻¹); unfold L R k; simp only [Function.comp_apply]; fun_prop

lemma drape (x : Y) : F.drape (move F d x)= gauge (k d S) (F.drape x) := by
   funext i; by_cases h:i∈ F.trunks
   · rw [Lattice.gauge,(show ∀ y:Y,F.drape y i=1 from fun y=> F.on_tree y ⟨i,h⟩) x,(show ∀ y:Y,F.drape y i=1 from fun y=> F.on_tree y ⟨i,h⟩)]; unfold k; simp [F.trunk_internal h]
   rw [(show ∀ y:Y, F.drape y i=y ⟨i,h⟩ from fun y=>F.off_tree y ⟨i,h⟩), Lattice.gauge,show F.drape x i=x ⟨i,h⟩ from F.off_tree x ⟨i,h⟩]; rfl
lemma color (y:G.El) : move F (fun (_: Site c)=>y) 1=1:= by funext i; change y * 1 * y⁻¹= 1; simp
private lemma noise_wears (U V : Config G c) (β:ℝ): S.noise β (gauge d U) (gauge d V)=S.noise β U V:= by
   unfold StepData.noise; apply Finset.prod_congr rfl; intro i _
   have he(u v x y:G.El): S.penaltyWeight β (u*x*v⁻¹*(u*y*v⁻¹)⁻¹)= S.penaltyWeight β (x*y⁻¹):=by unfold StepData.penaltyWeight; rw [show u*x*v⁻¹*(u*y*v⁻¹)⁻¹=u*(x*y⁻¹)*u⁻¹ by group,G.price_conj]
   simp only [Lattice.gauge, he]
variable {V : Type} [DecidableEq V] {T : Census V}
    (C : Lit T (Config G f)) (U' : Config G c) (β : ℝ)  (A : Set (F.Slice G))
lemma one (h : S.patch.Branches S.kernel G) (x:Y) (hw : GaugeInvariant C): stack w (gauge d U') β C (F.drape (move F d x))=stack w U' β C (F.drape x):= by
   unfold stack taggedKernel; rw [drape]; obtain ⟨he,hv⟩:= choice_gauge h (F.drape x) w (k d S); rw [he,hv,hw, show k d S ∘ S.ratio.embed=d by funext x; simp [k,Ratio.embed_parent],noise_wears]
theorem backswitch (h : S.patch.Branches S.kernel G) (hw : GaugeInvariant C):
    charge ν ((move F d '' A).indicator (stack w (gauge d U') β C ∘ F.drape))=charge ν (A.indicator (stack w U' β C ∘ F.drape)) := by
   let M : F.Slice G≃ₜ F.Slice G := move F d
   let p := ((M '' A).indicator (stack w (gauge d U') β C ∘ F.drape))
   have he : p ∘ M=A.indicator (stack w U' β C ∘ F.drape) := by
      funext x; by_cases ht:x∈A
      · unfold p; rw [Function.comp_apply,Set.indicator_of_mem (Set.mem_image_of_mem _ ht), Set.indicator_of_mem ht]; exact one F w d C U' β h x hw
      rw [Set.indicator_of_notMem ht]; exact Set.indicator_of_notMem (show M x∉ M '' A from by rintro ⟨b,hb,e⟩; exact ht ((M.injective e) ▸ hb)) _
   rw [← he]; ext t; rw [components,components]; exact ((preserves F d).integral_comp M.measurableEmbedding (atMark t p)).symm

private lemma open_color (y:G.El) (A : Set Y) (h : A∈𝓝 1) (p' : ℝ→ X) (hi : Tendsto p' along (𝓝 fun _=>y)) :
    ∃ Z∈𝓝 (1:Y), ∀ᶠ g in along,move F (p' g) '' Z⊆ A := by
    let f := fun z:X×Y=> move F z.1 z.2
    have he := (cont F (G:=G)).tendsto (((fun _ : Site c=>y),(1:Y)):X × Y); change Tendsto f _ _ at he
    rw [show move F (fun _ : Site c=>y) 1=1 from color ..] at he
    obtain ⟨a,ha,b,hb,H⟩:= mem_nhds_prod_iff.mp (he.eventually h)
    exact ⟨b,hb, (hi.eventually ha).mono fun g hg=> Set.image_subset_iff.mpr fun z hz=> H (a:=(p' g,z)) ⟨hg,hz⟩⟩
private lemma open_back (y:G.El) (A : Set Y) (h : A∈𝓝 1) (p' : ℝ→ X) (hi : Tendsto p' along (𝓝 fun _=>y)) :
    ∃ Z∈𝓝 (1:Y), ∀ᶠ g in along,(move F (p' g)).symm '' Z⊆ A := by
    let f := fun z:X×Y=> (move F z.1).symm z.2
    have he := (behind F (G:=G)).tendsto (((fun _ : Site c=>y),(1:Y)):X × Y); change Tendsto f _ _ at he
    rw [show (move F (fun _ : Site c=>y)).symm 1=1 from ((move F (fun _ : Site c=>y)).symm_apply_eq).2 (color F y).symm] at he
    obtain ⟨a,ha,b,hb,H⟩:= mem_nhds_prod_iff.mp (he.eventually h)
    exact ⟨b,hb, (hi.eventually ha).mono fun g hg=> Set.image_subset_iff.mpr fun z hz=> H (a:=(p' g,z)) ⟨hg,hz⟩⟩

-- actual finite bandwidth geometry. Use exactly same aperture equality. Simultaneous gauges
lemma law {A B : Set Y} (hA : A∈𝓝 1) (hB : B∈𝓝 1) (ha : IsOpen A) (hb : IsOpen B) (y:G.El) (p' : ℝ→X) (hp:Tendsto p' along (𝓝 fun _=>y)) :
    ∃ (f g:ℝ→Set (F.Slice G)), Liberty F f A ∧ Liberty F g B ∧ ∀ t,g t= move F (p' t) '' f t := by
    let p t:= move F (p' t); let f t:= A ∩ p t ⁻¹' B; let g t:= p t '' f t
    obtain ⟨C,hc,H⟩:= open_color F y B hB p' hp; obtain ⟨D,hd,G⟩:= open_back F y A hA p' hp
    have he t : g t=B∩(p t).symm ⁻¹' A := by ext z; simp [g,f,Homeomorph.image_eq_preimage_symm]; exact and_comm
    refine ⟨f,g,⟨A∩C, Filter.inter_mem hA hc, H.mono fun i hi=>?_⟩,⟨B∩ D, Filter.inter_mem hB hd,G.mono fun i hi=>?_⟩, fun _=>rfl⟩
    · exact ⟨Set.inter_subset_left,(ha.inter (hb.preimage (p i).continuous)).measurableSet,Set.inter_subset_inter_right _ (Set.image_subset_iff.mp hi)⟩
    rw [he]; exact ⟨Set.inter_subset_left,(hb.inter (ha.preimage (p i).symm.continuous)).measurableSet,Set.inter_subset_inter_right _ (Set.image_subset_iff.mp hi)⟩
end Switch
end YM.Comparison.RG02.Symmetry
