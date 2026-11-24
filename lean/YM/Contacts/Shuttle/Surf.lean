import YM.Contacts.Shuttle.Bow
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2500000
noncomputable section
namespace YM.Contacts.Shuttle.Tide
open Function Filter Finset Tensor Work Set MeasureTheory RG Wilson Lattice Labels Source Drops Analysis
open YM.MultiNext.SignedSource Powers Mediator Next.Foundations Pattern Broadcast Averaging Mom
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{V E : Type*}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]{m n d h b k:ℕ}
def curl (G:Gauge)(d:ℕ): Draft G d→ₗ[ℝ] Axis→ E4→G.Color:= LinearMap.pi (fun i:Axis=> LinearMap.pi (fun x:E4=> (fderiv ℝ (stereo G d ∘ shape (G:=G) (d:=d) x i) 0).toLinearMap))
lemma bounce (a: Draft G d)(x:E4)(i:Axis) : curl G d a i x=fderiv ℝ (stereo G d) 0 (shape x i a):= by
   let f:= stereo G d; let L:=shape (G:=G) (d:=d) x i
   change fderiv ℝ (f ∘ L) 0 a=_; have he:= derivative_shine x i (m:=1) (fun _=> a); rw [iteratedFDeriv_one_apply,iteratedFDeriv_one_apply] at he; exact he
-- Snap coefficient evaluation in arbitrary locations (not restricted to ℤ^4)
lemma traveled (i:Fin (d-1)) (v : Labels.Taylor G i.val) (x:E4)(a:Axis)(t:ℝ): field (tempo (d:=d) x a (Pi.single i v)) t=v.value a (x+t • basis a) := by
   unfold field; rw [Finset.sum_eq_single i]; · change Tensor.diagonal ((((Pi.single i v : Snap G d) i: Taylor G i.val).val a).compContinuousLinearMap _) _=_; rw [Pi.single_eq_same]; rw [← Pattern.line_at]; rfl
   · intro j _ hj; change Tensor.diagonal ((((Pi.single i v : Snap G d) j: Taylor G j.val).val a).compContinuousLinearMap _) _=_; rw [Pi.single_eq_of_ne hj]; rfl
   simp
lemma steady {f: E4→E}(h : f∈space E4 E 0)(x): f x=f 0:= by have ht:= (base h).2 0 x; simpa using ht.symm
-- physical momentum lemma: every request sees enough directions. Need degree n proper.
lemma launch {V : Axis→ E4→G.Color}(hi:0<h)(hd:h≤d)(hv:∀ i,V i∈ Powers.space E4 G.Color (h-1)) : ∃ v:Draft G d,v∈Jar G d h ∧ curl G d v=V:= by
   induction h using Nat.strongRecOn generalizing V with | _ l ih=>
   let L:= curl G d
   cases l; · omega
   rename_i n; cases n
   · obtain ⟨r,hR,H⟩:= sheet0 (Q:=V) (fun i=> base (hv i)); let v:Draft G d:= (-fit d r,0); have he : glow G.Color d v.1=-r:= by rw [show v.1=-fit d r from rfl,map_neg,sky (residence hR hd)]
     refine ⟨v,⟨he.symm ▸ (Powers.space E4 G.Color 1).neg_mem (residence hR le_rfl),fun _ _=>rfl⟩,funext fun i=>funext fun x=>?_⟩
     have hs : (∫ t in (0:ℝ)..1, D (basis i) r (x+t • basis i))= V i x:= by
       rw [intervalIntegral.integral_congr (g:=fun _=>V i x) (by intro t _; dsimp only; rw [← H]; exact (steady (hv i) _).trans (steady (hv i) x).symm)]; simp
     rw [differential (k:=0) hR] at hs; rw [bounce, first, shape_sound, sight,he,← hs]; simp only [v,map_zero]; simp [field, Tensor.diagonal]; abel -- cost
   rename_i j; choose P F hP hF hf using fun i=> roof (m:=j) (hv i); obtain ⟨r,T,hR,hA⟩:= Averaging.locale j (Q:=P) hP; let i:Fin (d-1):=⟨j,by omega⟩; let w:Draft G d:= (-fit d r,Pi.single i T); have he : glow G.Color d w.1=-r:= by rw [show w.1=-fit d r from rfl,map_neg,sky (residence hR hd)]
   have hw : w∈ Jar G d (j+2) := ⟨he.symm ▸ (Powers.space E4 G.Color (j+2)).neg_mem (residence hR le_rfl), fun a ha=> Pi.single_eq_of_ne (show a≠i by rintro rfl; exact lt_irrefl _ ha) _⟩ -- rfl h binder notation he? test
   let M a x := (∫ t in (0:ℝ)..1,P a (x+t • basis a))-P a x;
   have he' (a: Axis)(x:E4):curl G d w a x= ∫ t in (0:ℝ)..1,P a (x+t • basis a):= by
      have hp:=differential hR (basis a) x; rw [bounce, first, shape_sound, sight,he]; simp_rw [hA]; change (∫ t in (0:ℝ)..1,field (tempo (d:=d) x a (Pi.single i T)) t)- (-r _ - -r x)=_; simp_rw [traveled]; rw [intervalIntegral.integral_add, hp]; rotate_left; · exact (((diag_smooth (T.val a) 1).continuous).comp (by fun_prop : Continuous fun k:ℝ=>x+k • basis a)).intervalIntegrable _ _
      · exact (((graded hR (basis a)).1.continuous).comp (by fun_prop : Continuous fun k : ℝ => x+k • basis a)).intervalIntegrable _ _
      abel
   have hT (i: Axis) : (V-curl G d w) i∈ Powers.space E4 G.Color j:= by
      rw [show (V-L w) i= F i-M i from funext fun x=>by change V i x-curl G d w i x= F i x-M i x; rw [he' i x,hf i]; unfold M; simp only [Pi.add_apply]; abel] -- maybe rw L defeq tactic
      exact (Powers.space E4 G.Color j).sub_mem (hF i) (Averaging.buys (hP i) (basis i))
   obtain ⟨u,hu,hU⟩:= ih (j+1) (by omega) (by omega) (by omega) (V:=V-curl G d w) (fun i=> by simpa using hT i)
   refine ⟨w+u,(Jar ..).add_mem hw ⟨widen _ _ (by omega) hu.1, fun i hi=> hu.2 i (by omega)⟩,?_⟩; rw [map_add,hU]; abel
lemma rain_surj (he:d≤k) (hp:0<h)(hd:h≤d) (x:Ship G k)(ht:x∈Draws G k h): ∃ u∈Jar G d h,fderiv ℝ (rain G d k) 0 u=x:= by
   choose F H hF using ht; obtain ⟨u,hu,h⟩:= launch hp hd H; refine ⟨u,hu,funext fun i=>?_ ⟩; let M:=fun _ : Fin 1 => u; have he:= derivative_rain k i M; simp_rw [iteratedFDeriv_one_apply] at he; change fderiv ℝ (rain G d k) 0 u i=_ at he; rw [he,hF i]; apply congr_arg (fit (E:=G.Color) k); funext z; exact ((bounce u z i).symm.trans (congr_fun (congr_fun h i) z)) -- bounce
end YM.Contacts.Shuttle.Tide
