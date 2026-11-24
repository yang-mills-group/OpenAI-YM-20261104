import YM.OPE.Compatible.Birch.Postal
/-! # Linear image all cards paid. Lipschitz sector between two readings. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical
variable {I J W K:Type*} {i j n r d m:ℕ}{G:Gauge}{s b U D t ε:ℝ}{N:Side}
namespace Script
open Page
-- RegionB shape scales. all.
variable [Fintype J]
lemma region_nn (s C:ℝ)(b n m:ℕ)(hs:0<s):0 ≤ regionB J s C b n m:=by unfold regionB; have hv:=zero_le_one.trans (widthCost_ge hs m); unfold zest; positivity
lemma regionScale (s C D:ℝ)(b n m:ℕ)(he:0≤D): regionB J s (C*D) b n m= regionB J s C b n m * D^n:=by unfold regionB zest; rw [norm_mul, Real.norm_of_nonneg he];ring
variable {f g: K→ Script I r}{X w : K→ℝ}{A B:K→Cross N I J}
lemma clay (u:Cover)(ha:Tip s A 1 X)(hq:Loan m f w X)(hp:1 ≤ X)(hs:0<s):Loan m (fun i=>countermove (A i) u (f i)) w X:=by
     obtain ⟨a,ht,n,Ha⟩:=ha; obtain ⟨c,hc,m',Hq⟩:=hq; refine ⟨c * regionB J s a (size u) r m, mul_nonneg hc (region_nn s a _ _ _ hs),m'+n*r,fun i=>?_⟩
     have he:0≤ X i ^ n:=pow_nonneg (zero_le_one.trans (hp i)) _; have h: (A i).strip s (a*(X i)^n):=by simpa using Ha i
     refine (counterflow h hs (f i) _ (Hq i)).tips ?_; rw [regionScale s a _ _ _ _ he]; exact le_of_eq (by ring)
lemma sails (u:Cover)(ha:Tip s A 1 X)(hb:Tip s B 1 X)(hg:Tip s (A-B) w X)(hx:Loan m f 1 X)(hs:0<s)(hp:1 ≤ X)(hh:∀ i,0<w i):Loan m (fun i=>countermove (A i) u (f i)-countermove (B i) u (f i)) w X:=by
    obtain ⟨a₁,h₁,n,Ha⟩:=ha; obtain ⟨a₂,h₂,k,Hb⟩:=hb; obtain ⟨a₃,h₃,j,Hq⟩:=hg; obtain ⟨c,hc,l,Hf⟩:=hx
    let a:=max (max a₁ a₂) a₃; let y:=n+k+j; have ha:0 ≤ a:=h₃.trans (le_max_right ..); refine ⟨r*c*regionB J s (a+a+a) (size u) r m, mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hc) (region_nn _ _ _ _ _ hs), l+y*r,fun i=>?_⟩
    let t:=a*X i^y; have hp:= show 1 ≤ X i from hp i; have he(z:ℝ)(j:ℕ)(ht:z≤ a)(hv:j ≤ y)(hh:0≤z):z*X i^j ≤ t:=by unfold t; gcongr
    have hX:((A-B) i).strip s (w i*t):=by apply strip_mono (Hq i) le_rfl; rw [mul_comm (w i)]; refine mul_le_mul_of_nonneg_right (he _ _ (le_max_right ..) (Nat.le_add_left ..) h₃) (hh i).le
    have ha:(A i).strip s t:=by apply strip_mono (Ha i) le_rfl; rw [Pi.one_apply, mul_one]; apply he _ _ ((le_max_left ..).trans (le_max_left ..)) (by unfold y;omega) h₁
    have hb:(B i).strip s t:=by apply strip_mono (Hb i) le_rfl; rw [Pi.one_apply, mul_one]; apply he _ _ ((le_max_right ..).trans (le_max_left ..)) (by unfold y;omega) h₂
    apply (rakeChange ha hb hX (hh i) hs (p:=f i) u (Hf i)).tips; rw [show t+t+t=(a+a+a)*X i^y from by unfold t;ring, Pi.one_apply,regionScale _ _ _ _ _ _ (pow_nonneg (zero_le_one.trans hp) y)];exact le_of_eq (by ring)
lemma reachesC (u:Cover)(ha:Tip s A 1 X)(hb:Tip s B 1 X)(hv:Tip s (A-B) w X)(hx:Loan m f 1 X)(hQ:Loan m g 1 X)(hr:Loan m (f-g) w X)(hs:0<s)(hp:1 ≤ X)(hh:∀ i,0<w i):Loan m (fun i=>countermove (A i) u (f i)-countermove (B i) u (g i)) w X:=by
    have ht:=sails u ha hb hv hx hs hp hh; have he:=clay u hb hr hp hs; have h:=ht.seize he hp (fun i=> (hh i).le); convert! h using 1; funext i; simp only [Pi.add_apply,Pi.sub_apply]; have hh:Whole (B i):=by obtain ⟨A,-,n,g⟩:=hb; exact ⟨_,_,hs,g i⟩
    rw [show countermove (B i) u (f i-g i)=countermove (B i) u (f i)-countermove (B i) u (g i) from ?_]; abel
    obtain ⟨t,hv⟩:=Loan.cut hQ|>.bill i; change soot m (-g i) t at hv
    rw [sub_eq_add_neg, hoist hh u (hx.bill i|>.choose_spec) hv,show -g i=(-1:ℝ) • g i by simp,hoistS]; simp [sub_eq_add_neg]
end Script
end YM.OPE.Flume
