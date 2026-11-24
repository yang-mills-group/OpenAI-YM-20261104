import YM.PertExtension.PacketLimit

/-! Exact finite top/centered-cube identity and fast convergence for the
same-mask torus discrete symbol at fixed stencil offsets. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace YM.PertExtension.LatticePT
namespace Converter
open MeasureTheory Filter Topology Analysis Maxwell Asymptotics Next.Rank Next.Rank.Radian Set Real Metric Lattice Beamer CellsInt Wall Band
open Configuration Air Orb Orbit GaussianScore Function Finset Projection
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal RealInnerProductSpace FourierTransform
local notation "ℑ" => Complex.I
variable (p s:RG.Slot)(n:Side)

lemma aperture (j : Cover) (i:Axis):
    (-(1:ℝ)/2 < addr n j i ∧ addr n j i ≤ 1/2) ↔ (-(n.val:ℤ)<2*j i ∧ 2*j i ≤ n.val):=by
    rw [show addr n j i=(j i:ℝ)/n.val from div_eq_inv_mul .. |>.symm]
    have h:(0:ℝ)<n.val:=Nat.cast_pos.mpr n.pos
    rw [div_lt_div_iff₀ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    rw [neg_one_mul, one_mul, show (j i:ℝ)*2 = 2*(j i:ℝ) by ring]; constructor <;> intro h <;> exact_mod_cast h -- mul commuted?
lemma centered_lift (j : Cover):addr n j∈unitbox ↔ lift (wrap n j)=j := by
   unfold unitbox;rw [lift_eq_iff]; simp only [Set.mem_setOf_eq,true_and,and_self]; simp only [aperture]
lemma paper_funding (F: E4→ℝ) (h:∀ z∉unitbox,F z=0):
  (∑ i∈ room n 1,(↑(F (addr n i)):ℂ))=∑ x:Site n,↑(F (frequency x)) := by
    let Q:Cover→ℂ:= fun i => ↑(F (addr n i))
    let R:Finset (Site n):=Finset.univ
    let f:=lift (n:=n)
    have hu : Finset.image f R ⊆ room n 1 := by
       rintro i hi; obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hi
       have h j := lift_centers x j
       exact Finset.mem_Icc.mpr ⟨fun j=> show -(↑((1:ℕ)*n.val):ℤ)≤ lift x j from by have :=h j;omega,fun j=>show lift x _≤(↑((1:ℕ)*n.val):ℤ) from by have :=h j;omega⟩
    have hi:Function.Injective f:=fun i j h=>by unfold f at h; rw [← wrap_lift i,←wrap_lift j,h]
    change ∑ i∈room n 1,Q i=∑ i, Q (f i)
    have H (i) (hi:i∈room n 1)(he:i∉ Finset.image f R):Q i=0:= congr_arg Complex.ofReal (show F (addr n i)=0 from h _ (by
       rw [centered_lift]
       exact fun ht=> he (Finset.mem_image.mpr ⟨wrap n _,Finset.mem_univ _,ht⟩)))
    rw [← Finset.sum_subset (f:=Q) hu H, Finset.sum_image hi.injOn]

def plainPaper : E4→ℂ:= fun z=>(packet p s z:ℝ)
lemma paper_event : eventP 1 (plainPaper p s):= by intro z hz;unfold plainPaper packet;rw [indicator_of_notMem (fun h=>not_lt_of_ge (point_cover h) (by exact_mod_cast hz)),Complex.ofReal_zero]

def impulseSum (v:Momentum):ℂ:=LatticePT.phase p v * star (LatticePT.phase s v) * (∑ i:Axis,impulse p i v * star (impulse s i v))/ mass v

def vectorAt (u:Cover)(k:Site n):= pointAt (frequency k) -- unused param? remove
lemma tone_phase (t:RG.Slot)(k:Site n) :LatticePT.phase t (vectorAt n t.offset k) = tone (wrap n t.offset) k:=by
   rw (occs:=.pos [2]) [← wrap_lift k] -- problematic
   rw [phase_matches,terrel,chimes]
   unfold LatticePT.phase vectorAt; rw [PiLp.inner_apply]; congr 1
   change (((∑ i,(t.offset i:ℝ)*(radius*addr n (lift k) i)):ℝ):ℂ)*ℑ = 2*(π:ℂ)*ℑ*((∑ i:Axis, (t.offset i:ℝ) * addr n (lift k) i:ℝ):ℂ)
   unfold radius;push_cast;rw [mul_sum,sum_mul]; refine sum_congr rfl fun i _=> ?_; ring
lemma star_conjugate (k:Site n) (i j v):star (brief (gradient k) i j v)=brief (backward k) i j v:=by simp_rw [brief,star_gradient];split <;> split <;> simp [star_sub]

def position (t:RG.Slot):= (wrap n t.offset,t.plaq)
abbrev incline := disk (shining (position n s)) (position n p)

lemma impulse_gradient (t:RG.Slot) (k:Site n)(i:Axis):impulse t i (pointAt (frequency k)) = brief (gradient k) t.plaq.val.1 t.plaq.val.2 i:= by unfold impulse brief;simp_rw [← point_inc,← tone_step];rfl

lemma impulse_read (k:Site n):
    disk (lighting (position n s) k) (position n p)=(nV n)⁻¹ * impulseSum p s (pointAt (frequency k)) := by
  rw [position,disk_aug,disk_tone]
  unfold impulseSum; have h (t:RG.Slot):LatticePT.phase t (pointAt (frequency k)) = tone (wrap n t.offset) k:= tone_phase n t k
  have hr :∑ i,impulse p i (pointAt (frequency k))*star (impulse s i (pointAt (frequency k)))=
       wedge (gradient k) (weight (position n s) k) p.plaq.val.1 p.plaq.val.2 := by
      simp_rw [impulse_gradient,star_conjugate]
      unfold position weight
      exact (drops _ _ ..).trans (by rfl) -- fix
  rw [h p, h s,hr,unchanged_mass]
  unfold wrinkle; rw [position];dsimp only;rw [tone_star]; ring_nf <;> rfl

lemma impulse_project k :
    (disk (lighting (position n s) k) (position n p)).re = ((n.val:ℝ)^4)⁻¹ * packet p s (frequency k) :=by
   unfold packet; rw [indicator_of_mem (by
       exact (centered_lift ..).mpr (congr_arg _ (wrap_lift k))
     : frequency k ∈ unitbox)]; unfold bubble
   rw [impulse_read,nV,impulseSum,mul_sum,div_eq_mul_inv];simp_rw [← Complex.ofReal_natCast,← Complex.ofReal_pow,← Complex.ofReal_inv,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,Complex.re_sum]
   congr 1


end Converter
end YM.PertExtension.LatticePT
namespace YM.PertExtension.LatticePT.Converter
open MeasureTheory Filter Topology Analysis Maxwell Asymptotics Next.Rank Next.Rank.Radian Set Real Metric Lattice Beamer CellsInt Wall Band
open Configuration Air Orb Orbit GaussianScore Function Finset Projection
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal RealInnerProductSpace FourierTransform
variable (p s:RG.Slot)(n:Side)
lemma scan_real : (scansP n (plainPaper p s) 1).re= (incline p s n).re:=by
    unfold scansP
    let f:=packet p s
    have he:=paper_funding n f (show ∀z∉unitbox,f z=0 from fun z hz=> indicator_of_notMem hz _)
    change (((n.val:ℝ)⁻¹ ^ 4) • (∑ i∈room n 1, (↑(f (addr n i)):ℂ)):ℂ).re = _
    rw [he,RCLike.real_smul_eq_coe_smul (K:=ℂ), smul_eq_mul]
    change (Complex.ofReal _ * _).re=_; rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.re_sum,mul_sum,incline,disk_shining,Complex.re_sum]
    exact sum_congr rfl fun k _=>by rw [inv_pow];exact (impulse_project p s n k).symm
lemma sample_exact : (∫ z:E4, packet p s (port n z))=(incline p s n).re:=by
    obtain ⟨hT,H⟩:=grid_born n (plainPaper p s) 1 (paper_event p s)
    let f z:= packet p s (port n z)
    calc
     _ = (↑(∫ z:E4,f z):ℂ).re := rfl
     _ = (∫ z:E4, (f z:ℂ)).re:= by rw [integral_complex_ofReal]
     _ = (scansP n (plainPaper p s) 1).re:=congr_arg Complex.re H
     _ = _:=scan_real ..
local notation "reg"=> (atTop:Filter ℕ)
variable {q:ℕ+}(hq:1<q.val)
include hq
lemma incline_limit : Tendsto (fun t=> (incline p s (side q t)).re) atTop (𝓝 (kernelEntry p s)):= by simpa only [sample_exact] using limit_packet p s hq
end YM.PertExtension.LatticePT.Converter
