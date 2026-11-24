import YM.OPE.Compatible.Estuary.Pact
/-!
# Uniform version post-L. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Votive Tree
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n c f L:Side}{P:Patch}{K:KernelChoices}{I J:Type}{m k r d:ℕ}{σ C z:ℝ}
namespace Script
open Page Virgin Planned.PrimaryIntegral295.Carrier
lemma ready_kite (s:ℝ)(hs:0 < s)(P:Patch)(G:Gauge)(C:ℝ)(hc:0 ≤ C):∃ v t:ℝ,0 ≤ v∧ 0 < t∧∀ (A:Lines P.L),A.strip s C → (kite G P A).strip t v:=by
     obtain ⟨u,D,hu,hD⟩:= bow_price P; let t:=min s u; have ht:0 < t:=lt_min hs hu; let v:ℝ := Fintype.card (Co P.L (TypeFace 1)) * (D * C); refine ⟨max C v,t,hc.trans (le_max_left ..),ht,fun A h=>?_⟩; have he : A.strip t C:=strip_mono h (min_le_left ..) le_rfl; have hh: (straighter P A).strip t v:= strip_compose ht.le (strip_mono hD (min_le_right ..) le_rfl) he
     rintro ⟨i,j|j⟩ k
     · exact strip_mono (chrome_cost he hc) le_rfl (le_max_left ..) (i,j) k
     have hz:= forestWalk_pay (G:=G) (strip_mono hh le_rfl (le_max_right C v)) (hc.trans (le_max_left ..)); exact hz _ _
structure stint (q:(r:ℕ) → Script (Shade G) r) (r:ℕ)(Y:∀ n:Side,Config G n → ℝ):Prop where
    plot (i): ContDiffAt ℝ ω (Y i ∘ represent) 0
    wink (i k) : k ≤ r →  Voice (q k) (spool G i).toContinuousLinearMap (Y i∘ represent)
    stand i v u: Y i (Lattice.gauge v u)= Y i u
    here n: folk (q n)
    sym n :(q n).Idem
abbrev adjV (Z: Boxes G P K)(A:Lines P.L)(p: Script (Shade G) r):= stitch (player Z p)-payVolume (chrome G.ColorIndex A) p
lemma bias_rt (hs:0 <  σ)(P:Patch)(G:Gauge)(K:KernelChoices)(hC:0≤ C)(r m:ℕ):∃ v:ℝ,0 ≤ v∧∀ (H:Boxes G P K) (Y q)(A:Lines P.L), A.strip σ C →  Kine H A  →  stint q (r+1) Y → ∀ b,0≤ b →  (∀ i,i  <  r+1 →  0  < i →  soot m (q i) b) →  soot m (adjV H A (q (r+1))) (v*b):=by
    obtain ⟨D,h,H⟩:=stakeFog G (r+1) m (by omega); obtain ⟨U,t,hU,ht,htx⟩:=ready_kite _ hs P G _ hC; obtain ⟨B,hB,Hb⟩:=pokeBill ht hU m (r+1) (L:=P.L) (I:=Blend G) (J:=Shade G); let a:ℝ:=((r+1+1:ℕ):ℝ)^m; refine ⟨B*D*a,mul_nonneg (mul_nonneg hB h) (by unfold a; positivity),fun Y U q A hQ hv hg b hb hc=>?_⟩
    obtain ⟨p,hp,hd⟩:= H q b U hb (fun x hx ht=> hc x ht hx) (fun i=>⟨hg.plot i,hg.wink i,fun g k=>hg.stand i k g⟩)
    have hi : adjV Y A (q (r+1))= -stitch (payVolume (kite G P A) p):=by unfold adjV; rw [actor_slide _ _ ⟨_,_,hs,hQ⟩ hv (folk_whole (hg.here _)) (hg.sym _) (sootS hp) hd]; abel
    rw [hi]; have H!:= silt_cost (adjusted (Hb (kite G P A) (htx A hQ) p _ hp)); rw [show B*D*a*b=(B*(D*b))*a from by ring]; simpa only [soot,Sack,stitch, Pi.neg_apply,norm_neg] using H!
lemma hoistBoth {Z:Type*}{p:Z → (r:ℕ) → Script I r}{x v:Z → ℝ} (hX:1 ≤ x)(hv:0≤ v)(r:ℕ)(h:∀ i,i < r →  0  < i →  Loan m (fun j=>p j i) v x):∃ b:ℝ, 0≤ b∧∃ u:ℕ,∀ i j, i < r →  0  < i → soot m (p j i) (b*x j ^u * v j):=by
    induction r with
    | zero=>exact ⟨0,le_rfl,0,fun _ _ h=> by omega⟩
    | succ r ih=>
       obtain ⟨b,hb,u,H⟩:= ih (fun n hn=> h n (by omega)); by_cases hz:r=0; subst r; exact ⟨0,le_rfl,0,fun i j h h' => by omega⟩
       obtain ⟨c,hc,y,h⟩:= h r (by omega) (by omega); refine ⟨max b c,hc.trans (le_max_right ..),max u y,fun i j hi hj=>?_⟩; have hx:1 ≤ x j:= hX j; have hz: 0 ≤ v j:= hv j; by_cases he : i=r
       · subst i; apply (h j).tips; gcongr  <;>simp
       apply (H i j (by omega) hj).tips; gcongr  <;>simp
lemma fam_slides {Z:Type*}{p:Z → (r:ℕ) → Script (Shade G) r}{x v:Z → ℝ} (hX:1≤x)(hv:0 ≤ v){u:Z → Lines P.L}{H:Z → Boxes G P K}(h:∀ i,Kine (H i) (u i))(hs:0 < σ)(hA:∀ i,(u i).strip σ C)(hr:∀ i,∃ U, stint (p i) (r+1) U)(hy:∀ i, i  <  r+1 →  0  < i → Loan m (fun j=>p j i) v x): Loan m (fun i=> adjV (H i) (u i) (p i (r+1))) v x:=by
     obtain ⟨b,hb,B,hK⟩:= hoistBoth hX hv _ hy; obtain ⟨D,hD,hd⟩:=bias_rt hs P G K (le_max_right C 0) r m; refine ⟨D*b,mul_nonneg hD hb,B,fun i=>?_⟩; obtain ⟨U,hU⟩:=hr i; rw [show D*b*x i^B*v i=D*(b*x i^B*v i) from by ring]; refine hd (H i) _ _ (u i) (strip_mono (hA i) le_rfl (le_max_left ..)) (h i) hU _ (mul_nonneg (mul_nonneg hb (zero_le_one.trans (one_le_pow₀ (hX i)))) (hv i)) (fun j=> hK j i)
end Script
end YM.OPE.Flume
