import YM.OPE.Compatible.Speke.Cull
/-!
# Cohort mesh. Centers and support
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nestle
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush Maxwell Extra.FD SphereTest Analysis
open scoped BigOperators Classical ContDiff
open Balsam Port Extra.FD.OPE
variable {U:Gloam}{d r s:ℝ}{K:ℕ→ℕ}{k j l m:ℕ}{X Y Z: Panels} {A:Zem}
abbrev Crew (U:Gloam):={x:(i:ℕ)→Site (U.M i)// Drone U x}
def council (U:Gloam)(r:ℝ)(i:ℕ):= ⌊r*U.nb i⌋₊
lemma corral (U:Gloam)(hs:0 ≤ s) (i:ℕ): U.h i*council U s i ≤ s:=by
    have hx:= U.h_pos i; unfold council; have ht:= Nat.floor_le (mul_nonneg hs (Pert.Full.val_pos _|>.le): 0≤ s*U.nb i); grw [ht]; exact le_of_eq (by change (U.nb i)⁻¹*_= s; have hk:0<U.nb i:=Pert.Full.val_pos _; field_simp)
lemma widthCouncil (U:Gloam)(hs:0<s): Crown U (council U s):=by
   have hx:=corral U hs.le; constructor
   · refine ⟨s/2,by positivity,?_⟩; filter_upwards [U.h_null.eventually (gt_mem_nhds (by positivity : 0<s/2))] with i hi
     have hp : s ≤ U.h i*(council U s i+1:ℝ):=by
         have ht:=Nat.lt_floor_add_one (s*U.nb i); apply le_trans _ (mul_le_mul_of_nonneg_left ht.le (U.h_pos i).le); exact le_of_eq (by rw [show U.h i=(U.nb i)⁻¹ from rfl]; have hx:0<U.nb i:=Pert.Full.val_pos _; field_simp)
     linarith only [hi,hp]
   refine ⟨s+1,by positivity,?_⟩; filter_upwards [U.h_null.eventually (ge_mem_nhds zero_lt_one)] with i hi; have h:=hx i; linarith only [h,hi]
def rumB (p:Crew U)(i:ℕ)(x:Cover):= p.val i-wrap _ x
def rush (K:ℕ→ℕ)(x:Crew U)(i:ℕ):= (pod (K i)).image (rumB x i)
lemma rumSort (x:Crew U)(i:ℕ)(h:2*K i< (U.M i).val): InjOn (rumB x i) (pod (K i)):=by intro a ha b hb he; have hu: wrap (U.M i) a=wrap _ b:= sub_right_inj.mp (show x.val i-wrap (U.M i) a=x.val i-wrap (U.M i) b from he); rw [←gentle (n:=U.M i) (x:=a) (lt_of_le_of_lt (Nat.mul_le_mul_left _ (in_pod.mp ha)) h), ←gentle (n:=U.M i) (x:=b) (lt_of_le_of_lt (Nat.mul_le_mul_left _ (in_pod.mp hb)) h), hu]
lemma drum (v w:Crew U)(he:v.val 0=w.val 0):v=w:=by
   apply Subtype.ext; funext i; induction i with
   | zero=> exact he
   | succ i ih=>rw [v.property i,w.property i,ih]
lemma rush_dist (v w:Crew U)(i)(hx:2*(U.h i*K i)< seaRise U (v.val-w.val) 0): Disjoint (rush K v i) (rush K w i):=by
   apply Finset.disjoint_left.mpr; intro b h hp
   obtain ⟨x,hx',rfl⟩:=Finset.mem_image.mp h; obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hp; rw [←soar (z:=v.val-w.val) (fdroon v.property w.property) i] at hx; have hH: v.val i-w.val i =wrap _ x-wrap _ y :=by dsimp only[rumB] at he; symm; abel_nf at *; grind -- avoid
   change 2*_ < U.h i * pdist (v.val i-w.val i) at hx; rw [hH] at hx
   have hv:pdist (wrap _ x-wrap (U.M i) y) ≤ K i+K i:=by rw [sub_eq_add_neg]; exact (pdist_triangle ..).trans (Nat.add_le_add ((Next.Free.within_size ..).trans (in_pod.mp hx')) (pdist_neg (wrap _ y) ▸ ((Next.Free.within_size ..).trans (in_pod.mp hy))))
   have hh:= mul_le_mul_of_nonneg_left (show (↑(pdist (wrap _ x-wrap (U.M i) y)):ℝ)≤ ((K i+K i:ℕ):ℝ) by exact_mod_cast hv) (U.h_pos i).le; push_cast at hh; linarith only [hh,hx]
lemma guide (B:Finset (Crew U))(hs:0<s): ∃ R:ℕ→ℕ,Woody U R s ∧∀ i, 2*R i < (U.M i).val ∧ ∀ x∈B, ∀ y∈B,x≠y→Disjoint (rush R x i) (rush R y i):=by
   let A:= ((B ×ˢ B).filter (fun p=>p.1≠p.2)); have he(p:A):0<seaRise U (p.val.1.val-p.val.2.val) 0:= sea_pos (fun hh=> (Finset.mem_filter.mp p.property).2 (drum _ _ (sub_eq_zero.mp hh)))
   obtain ⟨r,h,hp⟩:∃ r>0, r<s∧2*r<1∧∀ p:A,2*r < seaRise U (p.val.1.val-p.val.2.val) 0:=by
       have hv(p:A):∀ᶠ x:ℝ in 𝓝 0,2*x<seaRise U (p.val.1.val-p.val.2.val) 0:=by exact ((show Tendsto (fun x:ℝ=>x) (𝓝 0) (𝓝 0) from tendsto_id)|>.const_mul 2).eventually (gt_mem_nhds (by simpa using he p)) -- Hint
       have ht:∀ᶠ x:ℝ in 𝓝 0,x<s∧2*x<1∧∀ p:A,2*x<seaRise U (p.val.1.val-p.val.2.val) 0:=by filter_upwards [gt_mem_nhds hs, gt_mem_nhds (by norm_num : (0:ℝ)<1/2),eventually_all.2 hv] with x hx h hy; exact ⟨hx,by linarith,hy⟩
       obtain ⟨x,hx,he⟩:= ((show ∀ᶠ z:ℝ in 𝓝[>] 0,0<z from self_mem_nhdsWithin).and (ht.filter_mono nhdsWithin_le_nhds)).exists; exact ⟨x,hx,he⟩
   obtain ⟨hs₁,hs₂,hs₃⟩:=hp; refine ⟨council U r, ⟨widthCouncil _ h, r,hs₁,Eventually.of_forall (corral U h.le)⟩, fun i=>⟨?_ ,fun x hx y hy hh=>?_⟩⟩
   · have ht:=corral U h.le i; have he: U.h i*U.nb i=1:=inv_mul_cancel₀ (Pert.Full.val_pos _).ne'; have hp : (↑(council U r i):ℝ)*2 < U.nb i:= by apply lt_of_mul_lt_mul_left (a:=U.h i) ?_ (U.h_pos i).le; linarith only [ht,he,hs₂]
     rw [mul_comm]; unfold Gloam.nb sizeR at hp; exact_mod_cast hp
   apply rush_dist; exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (corral U h.le i) zero_le_two) (hs₃ ⟨(x,y),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hy⟩,hh⟩⟩)
lemma behind (hp:Crown U K)(b:Crew U):∃ r>0,∀ᶠ i in atTop,∀ x:Site (U.M i),x∉ rush K b i→(r:ℝ) ≤ (pdist (b.val i-x):ℝ)*dew (U.M i):=by
   obtain ⟨r,h,H⟩:=hp.small; refine ⟨r/4,by positivity,?_⟩; filter_upwards [H] with i hi x hx; let y:=b.val i-x
   have he(p:Site (U.M i)):size (Lattice.lift p) ≤ 4*pdist p:=by
       unfold size
       calc _ ≤ ∑ j:Axis,pdist p:= Finset.sum_le_sum (fun j _=> component_le p j)
            _= _:=by simp
   have hh: K i < size (Lattice.lift y):=lt_of_not_ge fun h=>hx (Finset.mem_image.mpr ⟨Lattice.lift y,in_pod.mpr h, (by unfold rumB y; rw [wrap_lift,sub_sub_cancel])⟩)
   have ht:= mul_le_mul_of_nonneg_left (show (K i:ℝ) ≤ (4*pdist y:ℕ) from by exact_mod_cast hh.le.trans (he _)) (U.h_pos i).le; push_cast at ht; change r/4 ≤ (pdist y:ℝ)*U.h i; linarith only [ht,hi]
end YM.OPE.Nestle
