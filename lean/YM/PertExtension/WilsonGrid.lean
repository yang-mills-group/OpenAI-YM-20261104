import YM.PertExtension.Cosines

/-! The temporary band mask on frequency samples sums to an exact partition over
images -- it does not reweight the inversion quotient. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace YM.PertExtension.LatticePT.Band
open MeasureTheory Filter Maxwell Next Next.Rank Next.Rank.Radian Set Real Metric Lattice Beamer
open Function Finset ZMod
open scoped ContDiff Topology BigOperators Classical NNReal RealInnerProductSpace
variable {n:Side}

abbrev Flags := Axis → Bool
private def offset (n:Side) (b:Bool): ℤ:= if b then n.val else 0
def spray (k:Site n) (p:Flags) : Cover := fun i:Axis=> ((k i).val:ℤ)-offset n (p i)
lemma spray_site (k:Site n) (p) : wrap n (spray k p)=k:= by
   ext i;change (((((k i).val:ℕ):ℤ)-offset n (p i):ℤ):ZMod n.val) = k i
   unfold offset; split <;> push_cast <;> simp
lemma numbers (i : Site n × Flags): spray i.1 i.2∈ room n 2:= by
   obtain ⟨k,p⟩:=i; refine Finset.mem_Icc.mpr ⟨?_,?_⟩ <;> intro i <;> have h: (k i).val<n.val:=ZMod.val_lt _
   · change -(↑(2*n.val):ℤ)≤spray k p i;unfold spray offset;split <;> omega
   change spray k p i ≤ (↑(2*n.val):ℤ);unfold spray offset;split <;> omega
lemma split_spray (n:Side): Injective (fun i:Site n×Flags=>spray i.1 i.2):=by
   rintro ⟨k,p⟩ ⟨l,t⟩ e
   have h : k=l:= by simpa only [spray_site] using congr_arg (wrap n) e
   refine Prod.ext h ?_ ; funext i;subst l
   have ht: n.val > 0:=n.pos
   have he : ((k i).val:ℤ)-offset n (p i)= ((k i).val:ℤ)-offset n (t i):=congr_fun e i
   cases hp:p i <;> cases hv:t i <;> simp [offset,hp,hv]  at he <;> first | { change p i=t i; rw [hp,hv] } | { simp_rw [← ZMod.natCast_val] at he; omega }
lemma site_difference (t : Cover) (i): ((n.val:ℕ):ℤ) ∣ t i - (((wrap n t i:ZMod n.val).val:ℕ):ℤ):= by
   apply (intCast_eq_intCast_iff_dvd_sub ..).mp; push_cast
   change ((wrap n t i).val:ZMod n.val)=(wrap n t i);exact ZMod.natCast_zmod_val _
private lemma in_mask {t:Cover}(h:hood (addr n t)≠0) : ∃ p:Flags,t=spray (wrap n t) p:=by
   suffices hp:∀ i:Axis,∃ b:Bool,t i=(((wrap n t i).val:ℕ):ℤ)-offset n b by
      choose b hb using hp;exact ⟨b,funext fun i=>hb i⟩
   intro i
   have hx:|addr n t i| < 3/4:= lt_of_not_ge (fun hor=>h (Finset.prod_eq_zero (Finset.mem_univ i) (tent_small hor)))
   let c:= (wrap n t i).val
   have hc:=ZMod.val_lt (n:=n.val) (wrap n t i)
   let r:ℤ:=n.val
   have hl:0 < r:=Int.natCast_pos.mpr n.pos;have hr:(0:ℝ)<n.val:=Nat.cast_pos.mpr n.pos
   have hv:= site_difference (n:=n) t i
   obtain ⟨b,hb⟩ : r∣ t i - (c:ℤ):= hv
   have hx': (addr n t i)= ((t i):ℝ)/n.val := div_eq_inv_mul ..|>.symm
   rw [hx'] at hx
   obtain ⟨hx₁,hx₂⟩:=abs_lt.mp hx
   have h₁ := (div_lt_iff₀ hr).mp (lt_of_lt_of_le hx₂ (by norm_num : (3/4:ℝ)≤1))
   have h₂:= (lt_div_iff₀ hr).mp (lt_of_lt_of_le (show (-1:ℝ)< -3/4 by norm_num) (by linarith : (-3/4:ℝ)≤t i/ (n.val:ℝ)))
   rw [one_mul] at h₁;rw [neg_one_mul] at h₂
   have hi : -2*r < t i-c ∧ t i -c <r:= by
       have h':t i<r:=by exact_mod_cast h₁
       have h'': -r < t i:=by exact_mod_cast h₂
       omega
   obtain rfl|hb' :b=0 ∨ b=-1:= by have := nlinarith_aux hb hi hl; omega -- adjust proof
   · exact ⟨false,by dsimp [offset]; omega⟩
   exact ⟨true,by dsimp [offset];subst b;omega⟩
where
  nlinarith_aux {r c x b : ℤ}(h : x-c=r*b)(hx : -2*r<x-c∧x-c<r)(hr : 0 <r) : -2<b ∧ b<1 := ⟨lt_of_mul_lt_mul_left (by rw [←h];simpa [mul_comm] using hx.1) hr.le,lt_of_mul_lt_mul_left (by rw [←h];simpa using hx.2) hr.le⟩

private lemma complements (x : ℝ): smoothTransition x + smoothTransition (1-x)=1:= by
    unfold smoothTransition;rw [show 1-(1-x)=x by abel]; rw [add_comm (expNegInvGlue (1-x)),← add_div]; exact div_self (smoothTransition.pos_denom x).ne' -- maybe denom ordered
lemma halves (z : ℝ) (h:0≤ z)(hz : z≤1) : tent z+tent (z-1)=1:=by
   rw [tent,tent,rise_zero (u:=-z) (by linarith),rise_zero (u:=z-1) (by linarith)]
   unfold rise;rw [show 2*(-(z-1))-1/2=1-(2*z-1/2) by ring]; push_cast
   have he:=congr_arg (fun x:ℝ=> (↑x:ℂ)) (complements (2*z-1/2)); push_cast at he
   linear_combination -he
lemma flags_tent (k:Site n) (i) : ∑ b:Bool,tent ((1/(n.val:ℝ)) * (((k i).val:ℝ)- offset n b))=1 := by
    simp_rw [offset]; rw [Fintype.univ_bool]
    simp; rw [← ZMod.natCast_val]
    change tent ((n.val:ℝ)⁻¹ * (((k i).val:ℝ)-n.val)) + tent ((n.val:ℝ)⁻¹ * ((k i).val:ℝ)) = 1
    rw [show (n.val:ℝ)⁻¹ * (((k i).val:ℝ)-n.val) = (n.val:ℝ)⁻¹*((k i).val:ℝ)-1 by have h:(n.val:ℝ)≠0:=mod_cast n.pos.ne'; field_simp[h],add_comm]
    apply halves
    · positivity
    rw [← div_eq_inv_mul];apply (div_le_iff₀ (by positivity)).mpr
    rw [one_mul]
    all_goals exact_mod_cast (show (k i).val≤n.val from (ZMod.val_lt _).le)
lemma hood_partition (k:Site n): ∑ b:Flags,hood (addr n (spray k b))=1:= by
  let W (i:Axis)(b:Bool):ℂ:= tent (1/(n.val:ℝ)*(((k i).val:ℝ)-offset n b))
  have he i : ∑ t: Bool,W i t=1 := flags_tent k i
  calc
     _ = ∑ b:Flags, ∏ i, W i (b i):= by
       apply Finset.sum_congr rfl fun p _=>Finset.prod_congr rfl fun i _=> ?_
       change tent ((n.val:ℝ)⁻¹ * ((spray k p i:ℤ):ℝ))= _
       unfold W spray offset; congr 1; push_cast; ring
     _ = _:= by rw [←Fintype.prod_sum]; simp_rw [he,Finset.prod_const_one]

lemma spray_sum (n:Side) (F : Cover→ℂ) (h:∀ j:Cover,hood (addr n j)=0 → F j=0) :
   (∑ j∈ room n 2,F j)=∑ k:Site n,∑ b:Flags,F (spray k b):= by
  let M:Finset Cover:=(Finset.univ (α:=Site n×Flags)).image (fun v=> spray v.1 v.2)
  have ht: M⊆ room n 2:= fun q h=>by obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp h;exact numbers v
  rw [← Finset.sum_subset (f:=F) ht,Finset.sum_image (split_spray n).injOn
  ]
  · exact Fintype.sum_prod_type (fun v=> F (spray v.1 v.2))
  intro x _ hn;apply h
  by_contra hs;apply hn
  obtain ⟨p,hv⟩:=in_mask hs;exact Finset.mem_image.mpr ⟨(wrap n x,p),Finset.mem_univ _,hv.symm⟩

end YM.PertExtension.LatticePT.Band
