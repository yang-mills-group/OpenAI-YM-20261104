import YM.FVA2.BareMetric
/-!
# Use of PS coordinates with the position extraction kernel. Jets and prescription powers.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace YM.FVA2.WorldJet
open Function Filter Set PositionX PositionX.Jet
open MS.Book MS.Book.Program MS.Book.Convolve Complex
open Clock Attend
open PowerSeries
open scoped Topology ContDiff Classical
variable {n m:ℕ} {A B:Cn} {f g:ℝ→ℂ}
-- helper
lemma step_h (s:ℂ): out (PowerSeries.C s)= just s:= funext fun i=> by rw [ out_coeff,PowerSeries.coeff_C ]; unfold just; split <;> simp_all
lemma badge (s:ℂ): Act n (fun _:ℝ=>s) (out (PowerSeries.C s)):= by rw [step_h]; exact Act.static _
lemma step_z : Act n (0:ℝ→ℂ) (out 0):=by simpa only [map_zero,Pi.zero_def] using (badge (n:=n) 0)
lemma step_s (hf:Act n f (out A))(hv:Act n g (out B)): Act n (f+g) (out (A+B)):= by rw [map_add]; exact hf.add hv
lemma step_ℤ (f:ℂ): Act n (fun _:ℝ=>f) (out (PowerSeries.C f)):= badge f
lemma beget (hf:Act n f (out A))(hv:Act n g (out B)): Act n (f*g) (out (A*B)) := by
    refine ⟨ hf.nice.mul hv.nice,fun t h=>?_⟩; unfold someJ; rw [iteratedDeriv_mul (hf.nice.of_le le_top) (hv.nice.of_le le_top), Finset.smul_sum, out_coeff, coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ (f:=fun i j=> coeff i A * coeff j B) ]; refine Finset.sum_congr rfl fun i hi=> ?_; have he:= Finset.mem_range.mp hi;
    rw [hf.actual i (by omega),hv.actual (t-i) (by omega) ]; simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ), Clock.out_coeff, smul_eq_mul ]; push_cast; have hz :(t.choose i:ℂ)* (i.factorial:ℂ)*(Nat.factorial (t-i):ℂ)=(t.factorial:ℂ):= (by exact_mod_cast Nat.choose_mul_factorial_mul_factorial (Nat.lt_add_one_iff.mp he))
    have hb:( t.factorial:ℂ )≠0:= Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _); field_simp; rw [← hz]; ring
lemma big (hf:Act n f (out A))(k:ℕ): Act n (f^k) (out (A^k)):= by induction k with| zero=> simp only [pow_zero]; exact (map_one (PowerSeries.C (R:=ℂ))) ▸ step_ℤ 1| succ k ih=> rw [pow_succ,pow_succ]; exact beget ih hf
lemma forAll {ι:Type*}(s:Finset ι){f:ι→ℝ→ℂ}{g:ι→Cn}(hv:∀ i∈s,Act n (f i) (out (g i))): Act n ( ∏ i∈s,f i ) (out (∏ i∈s,g i)):= by classical induction s using Finset.induction with| empty=> rw [Finset.prod_empty,Finset.prod_empty]; exact (map_one (PowerSeries.C (R:=ℂ))) ▸ step_ℤ 1| insert p s hp ih=> rw [ Finset.prod_insert hp,Finset.prod_insert hp ]; exact beget ( hv p (by simp)) ( ih fun i hi=> hv i (Finset.mem_insert_of_mem hi))
lemma summ {ι:Type*}(s:Finset ι){f:ι→ℝ→ℂ}{g:ι→Cn}(hv:∀ i∈s,Act n (f i) (out (g i))): Act n ( ∑ i∈s,f i ) (out (∑ i∈s,g i)):= by classical induction s using Finset.induction with| empty=> rw [Finset.sum_empty,Finset.sum_empty]; exact step_z| insert p s hp ih=> rw [ Finset.sum_insert hp,Finset.sum_insert hp ]; exact step_s ( hv p (by simp)) ( ih fun i hi=> hv i (Finset.mem_insert_of_mem hi))
lemma ref_frame (x:Word ℝ) (H:light x) (A B:Cn)(hv:(Complex.ofReal ∘ x)= out B): out (stencil B A)= ren x (out A) := by
   funext n; let U:=Finset.range (n+1); let c:= coeff (R:=ℂ); let f:ℝ→ℝ:= delay x n; let v:ℝ→ℂ:= fun i=> ↑(f i); let g:= delay (out A) n;
   let V(i:ℕ):= PowerSeries.C (c i A)*B^i; have hf:Act n f x:= Act.swell x le_rfl; have hv0: Act n v (out B):= by rw [ ← hv ]; exact hf.linear (L:=Complex.ofRealCLM)
   let ℓ (i:ℕ):= (fun x:ℝ=>c i A)*v^i; have he : Act n (∑ i∈U,ℓ i) (out (∑ i∈U,V i)):= summ U (fun i hi=> beget (step_ℤ _) (big hv0 _))
   have hh:∑ i ∈ U,ℓ i= g ∘ f:= by ext1 t; unfold g delay ℓ; dsimp only [Function.comp_apply]; rw [ Finset.sum_apply ]; apply Finset.sum_congr rfl; intro i hi; simp only [ Pi.mul_apply,Pi.pow_apply, Clock.out_coeff, Complex.real_smul, Complex.ofReal_pow ]; unfold c v; ring
   have hz:(out (stencil B A)) n=(out (∑ i∈U,V i)) n:= by
       rw [ gradeS,rules,map_sum, Finset.sum_apply, show Finset.Iic n=U from Finset.ext (by simp only [Finset.mem_Iic,U,Finset.mem_range];omega) ]; refine Finset.sum_congr rfl fun i _=>?_; unfold V c; rw [out_coeff,out_coeff,coeff_C_mul,smul_eq_mul,mul_comm ]
   rw [hh] at he; exact hz.trans (he.trans_at (hf.dial (hp:=Act.swell (out A) le_rfl) H) le_rfl) -- syntax
lemma ren_clock (p:Team)(x:ℝ)(A:Cn) : out (stencil (shift p x) A)= ren (fun i=>coeff i (Clock.rate p x)) (out A) := by
    apply ref_frame; exact Clock.rooted ..; funext i; rw [ bare_shift,out_coeff,coeff_map ]; rfl
end YM.FVA2.WorldJet
