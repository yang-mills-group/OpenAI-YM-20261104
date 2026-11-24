import YM.WilsonCoeffUV.Winding.Alias
/-!
# Uniform capped hulls.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.WilsonCoeffUV.Winding
open Wheel Wheel.Mark Cosmos Mer Function Filter Lattice RG Embroider Soil Bank Laurent Bloch Metric Gauge Power Matrix Precision Wilson Tree Exterior Blue Work.F08 FreeResolvent AnalyticNext.QuarticMatch.Sheets PowerSeries Bank.Mosaic Bank.Carp
open scoped Topology BigOperators
variable {n L:Side}{ι U X α β V:Type}{G:Gauge}{D k:ι→ℕ}{i j r e a l:ℕ}{s A B C W t q :ℝ}
variable {J Z S:Finset ι}{p:ι→Cover}

lemma post_wage {r d:ℕ}(p:4*d<r)(v:0≤s): catchW s r≤ catchW (s/2) r * catchW (s/2) d:=by
   unfold catchW; rw [← Real.exp_add,Real.exp_le_exp]; have hp:d≤r:=by omega
   have hz:=mul_le_mul_of_nonneg_left (show (d:ℝ)≤r from by exact_mod_cast hp) v; linarith
lemma post_loss {r d:ℕ}(p:r≤8*d)(v:0≤s): catchW s d≤ catchW (s/16) r * catchW (s/2) d:=by
   unfold catchW; rw [←Real.exp_add,Real.exp_le_exp]; have hp:(r:ℝ)≤8*d:=by exact_mod_cast p
   linarith [mul_le_mul_of_nonneg_left hp v]
variable [NormedAddCommGroup V]
lemma decr {x y z:V}{i d:ℕ}(h:‖x-z‖≤ A*catchW s i)(p:‖y-z‖≤ B*catchW s i)(v:4*d < i)(b:0≤s)(hx:0≤A+B) : ‖x-y‖≤ (A+B)*catchW (s/16) i* catchW (s/2) d:=by
    rw [show x-y= (x-z)-(y-z) from by abel]; apply (norm_sub_le ..).trans ((add_le_add h p).trans _); rw [←add_mul,mul_assoc]; exact mul_le_mul_of_nonneg_left ((post_wage v b).trans (mul_le_mul_of_nonneg_right (catch_width (by linarith) _) (catch_hot ..))) hx
lemma expired {x y:V}{i d:ℕ}(h:‖x‖≤ A*catchW s d)(p:‖y‖≤ B*catchW s d)(v:i≤8*d)(b:0≤s)(hx:0≤A+B): ‖x-y‖≤ (A+B)*catchW (s/16) i* catchW (s/2) d:=by
   apply (norm_sub_le ..).trans ((add_le_add h p).trans _); rw [← add_mul,mul_assoc]; exact mul_le_mul_of_nonneg_left (post_loss v b) hx
abbrev windPay (s A:ℝ)(i:ℕ):= A*(hinges s i+1)+A
lemma costOrbit {F:post G i}{P:Ten ℝ (Co n (Hooks G)) (i+1)}(h:Sight P F s A)(v:0<s)(q:stroll F): let t:=perchA s i
    Amber (tor n) (t/2) (windPay s A i*catchW (t/16) n) (lagoon F n-P):=by
    intro t; let B:= A*(hinges s i+1); let K:= lagoon F n; have hv:=h.mono (min_le_left s (hingeZ s i/2));
    have hu:=bridgeA (n:=n) h.bound v q; have hx:= hv.aim; have ht:=hu.aim; have ha:=hv.gall; have hg:= hu.gall; rw [pruce_down] at hx ht ha hg
    have hB:= add_nonneg ht.1 hx.1; have hs:= (perch_pos v i).le; refine ⟨mul_nonneg hB (catch_hot ..),fun x=>?_⟩
    let b:= lift (x 0).1; let y:= unfoldAt b x; have he:soar Bank.terrain y≤ 2*soar (tor n) x := by
       apply league_cash _ (a:=b); intro i; change Bank.terrain.gap b ((unfoldAt b x) i).1≤_; unfold b; rw [near_change,wrap_lift]; exact leg_le (tor n) (Prod.fst ∘ x) 0 i
    by_cases p:4*soar Bank.terrain y < n.val
    · have hZ:= decr (hg.local_w y p) (ha.local_w y p) p hs hB
      have hz : soar Bank.terrain y=soar (tor n) (slideC n y) := (exact_course (x:=Prod.fst ∘ y) p).symm; rw [hz,show slideC n y=x from slides_back b x] at hZ; exact hZ
    have hp : n.val≤8*soar (tor n) x:=by omega
    exact expired (ht.2 x) (hx.2 x) hp hs hB

lemma soarW (d:Bank.Distance U)(p:ι→U)(J:Finset ι)(x:dock U α r): soar d x≤ Syn d p J x:= by apply reachL; intro i; exact ⟨.inr i,rfl⟩
abbrev crestCard (p:ι→Cover)(J:Finset ι): ℕ:= league Bank.terrain (fun i:J=>p i.val)
lemma marks_bill {u:ι}(p:ι→Cover)(J)(q:u∈J)(b:4*crestCard p J<n.val)(x:dock (Site n) α r): Syn Bank.terrain p J (unfoldAt (p u) x)≤2*Syn (tor n) (wrap n ∘ p) J x:=by
   let t:= p u; apply league_cash _ (a:=t); intro i; cases i with
   | inl i=>
       let y (i:J):=p i.val; apply (show Bank.terrain.gap t (y i)≤ league Bank.terrain y from leg_le Bank.terrain y ⟨u,q⟩ _).trans
       rw [← exact_course b]; apply reachL; intro j; exact ⟨.inl j,rfl⟩
   | inr i=>
       rw [show foyer p J _ _=((unfoldAt (p u) x) i).1 from rfl, near_change]; exact leg_le (tor n) (foyer (wrap n ∘ p) J x) (.inl ⟨u,q⟩) (.inr i)
variable [CompleteSpace V][Fintype α]
lemma markOrbit {F:Ten V (Cloth α) i}{Q: Ten V (Co n α) i}(h: MarkU p J Q F s A)(u:J.Nonempty)(b:4*crestCard p J<n.val)(v:0<s): let t:=s/32; let B:=(priceM α i s+tiePay α i (s/4)+1)*A+A
     Wig (tor n) (wrap n ∘ p) (t/2) (B*catchW (t/16) n) J (Bank.Carp.plume F n-Q):=by
    intro t B; have hx:=h.mono (show t≤s from by unfold t; linarith); have ht:=plumeW (n:=n) h.access u v; have hB:=add_nonneg ht.bill.1 hx.bill.1; have hp:0≤t:=by unfold t; positivity
    refine ⟨mul_nonneg hB (catch_hot ..),fun x=>?_⟩; obtain ⟨k,i⟩:= u; let y:=unfoldAt (p k) x
    have he : slideC n y=x:= slides_back ..
    have hv:= marks_bill p J i b x
    by_cases hb:4*Syn Bank.terrain p J y<n.val
    · have hz:=decr (ht.gulf.local_w _ hb) (hx.gulf.local_w _ hb) hb hp hB; rw [← exact_syn p J y hb,he] at hz; exact hz
    have hz:n.val≤8*Syn (tor n) (wrap n∘ p) J x:=by unfold y at hb; omega
    exact expired (ht.bill.2 x) (hx.bill.2 x) hz hp hB
end YM.WilsonCoeffUV.Winding
