import YM.FormalBulk08.Mesa.Rift

/-! All alphabets before active reduction. Blocks coarse/fine tags. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Bank
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Matrix Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F08 Flat Mesa
open scoped Topology ENNReal BigOperators Classical ContDiff
variable {V I : Type*} {L m n : Side}

def scroll (L : Side) (I : Type*) : Biglot I≃ Biglot (Tor L I) where
   toFun x := (rent L x.1,wrap L x.1,x.2)
   invFun x := (lift x.2.1+L.val • x.1,x.2.2)
   left_inv x := Prod.ext (rent_balance L x.1).symm rfl
   right_inv x:= let h:=rent_raw (L:=L) x.1 _ x.2.1 rfl; Prod.ext h.2 (Prod.ext h.1 rfl)
lemma scroll_big (x : Biglot (Tor L I)) : ((scroll L I).symm x).1=lift x.2.1+L.val • x.1:=rfl
lemma scroll_pull (x : Biglot I) (S : Ratio m n) : drip m (scroll S.count I x)= splitCo S I (drip n x) := by
   apply (splitCo S I).symm.injective
   rw [Equiv.symm_apply_apply]; apply Prod.ext
   · change S.assemble (wrap m (rent _ x.1),wrap S.count x.1)=wrap n x.1; rw [Ratio.assemble,Ratio.embed_wrap, add_comm,←map_add,←rent_balance (S.count) x.1]
   rfl
lemma scroll_tint (L : Side) (y : Cover) (x : Biglot (Tor L I)) : (scroll L I).symm (Lotus.tint y x) = Lotus.tint (L.val • y) ((scroll L I).symm x) := by
   apply Prod.ext
   · rw [tint_fst,scroll_big,scroll_big,tint_fst,tint_snd]; rw [smul_add,add_assoc]
   rfl
lemma packed_up {r : ℕ} {T : Tile (Biglot I) r} (hp : Up T) (L : Side) : Up (jetty (scroll L I).symm T) := by
   intro x v; change T _=T _; refine Eq.trans ?_ (hp (L.val • x) _); apply congr_arg T; exact funext fun _=> scroll_tint ..

-- Commuting absolute representation with wrapping, any i
lemma cum_jet {m : Side} {n : Side} (S : Ratio m n) {r : ℕ} (T : Tile (Biglot I) r) (hp : Up T) (i : Fin r) :
    cum i m (jetty (scroll S.count I).symm T)=jetty (splitCo S I).symm (cum i n T):= by
   funext v; let V:=(splitCo S I).symm ∘ v
   let x:=boil m (v i); let k:=scroll S.count I;let f:= splitCo S I; let W := f.symm ∘ v
   change cum i m _ v=cum i n T W; have hh (j:Biglot (Tor S.count I)) : drip n (k.symm j)= f.symm (drip m j) := by apply f.injective; rw [f.apply_symm_apply]; exact (by simpa [k,f] using (scroll_pull (k.symm j) S).symm)
   rw [cum_near _ n hp W (k.symm x) (by rw [hh]; simp [x,W])]; change (∑' w:Picks i m x v,T (k.symm ∘ w.val))= _
   let e : Picks i m x v≃ Picks i n (k.symm x) W:=⟨fun w=>⟨k.symm ∘ w.val,(by rw [Function.comp_apply,w.property.1]),funext fun j=>by rw [Function.comp_apply,Function.comp_apply,hh]; exact congr_arg f.symm (congr_fun w.property.2 j)⟩,
      fun w=>⟨k ∘ w.val,(by rw [Function.comp_apply,w.property.1, k.apply_symm_apply]),funext fun j=>by change drip m (scroll S.count I _)=_;rw [scroll_pull]; exact (congr_arg f (congr_fun w.property.2 j)).trans (f.apply_symm_apply _)⟩,
      fun w=>Subtype.ext (funext fun j=>k.apply_symm_apply _), fun w=>Subtype.ext (funext fun j=>k.symm_apply_apply _)⟩
   exact Equiv.tsum_eq e (fun w=> T w.val)
-- growth shift in own units
lemma extent_ray (x y : Biglot (Tor L I)) : L.val*capD x.1 y.1 ≤ capD ((scroll L I).symm x).1 ((scroll L I).symm y).1+8*L.val := by
   let a:=((scroll L I).symm x).1;let b:=((scroll L I).symm y).1
   have he (v:Site L) : size (lift v) ≤ 4 * L.val := by
       have hh : ∑ k:Axis,(lift v k).natAbs ≤ ∑ _ : Axis,L.val := by
          refine Finset.sum_le_sum fun k _=>?_ ;have h:=lift_centers v k;omega
       simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin, Laurent.size,smul_eq_mul] using hh
   rw [show L.val*capD x.1 y.1 = size (L.val • (x.1-y.1)) by unfold capD; simp [size,Finset.mul_sum,Int.natAbs_mul]]
   have ht : L.val • (x.1-y.1)=(a-b)+lift y.2.1+ -(lift x.2.1) := by simp_rw [a,b,scroll_big,nsmul_sub];abel
   rw [ht]; change _ ≤ size (a-b)+_
   have h:=size_add ((a-b)+lift y.2.1) (-lift x.2.1); have hx:=size_add (a-b) (lift y.2.1); rw [size_neg] at h; have hu:=he x.2.1;have hz:=he y.2.1;omega
lemma unfold_wide {r : ℕ} (v : chain (Biglot (Tor L I)) r):
    L.val*wide (fame _) v ≤ wide (fame _) ((scroll L I).symm ∘ v)+8*L.val:= by
   let B:= wide (fame _) ((scroll L I).symm ∘ v)+8*L.val;rw [Nat.mul_comm]; refine (Nat.le_div_iff_mul_le L.property).mp (known_wide _ _ _ fun i j=>?_)
   apply (Nat.le_div_iff_mul_le L.property).mpr;rw [Nat.mul_comm]; apply (extent_ray _ _).trans (Nat.add_le_add_right ?_ _); exact reached (fame _) ((scroll L I).symm ∘ v) i j
lemma shift_wide {r : ℕ} {σ τ : ℝ} (L : Side) (v : chain (Biglot (Tor L I)) r) (h : τ ≤ L.val * σ) (he : 0 ≤ τ) :
    shine τ (wide (fame _) v) ≤ ENNReal.ofReal (Real.exp (8*τ))*shine σ (wide (fame _) ((scroll L I).symm ∘ v)) := by
   let a:= wide (fame _) v; let z:=wide (fame _) ((scroll L I).symm ∘ v)
   have hp : (L.val:ℝ)*a≤(z:ℝ)+8*L.val:=by exact_mod_cast unfold_wide v
   unfold Gorge.shine; rw [←ENNReal.ofReal_mul (Real.exp_pos _).le,←Real.exp_add]; apply ENNReal.ofReal_le_ofReal; apply Real.exp_monotone
   change τ*a ≤ 8*τ+σ*z; let x:ℝ:=L.val; have hx : 0<x :=by unfold x; positivity
   apply le_of_mul_le_mul_left _ hx
   calc _ = τ*(x*a):=by ring
        _ ≤ τ*(z+8*x):= mul_le_mul_of_nonneg_left hp he
        _ ≤ x*(8*τ+σ*z):= by rw [mul_add, mul_add x];nlinarith only [mul_le_mul_of_nonneg_right (show τ≤x*σ from h) (Nat.cast_nonneg z : (0:ℝ) ≤ (z:ℝ))]
lemma packet_bill {r : ℕ} {σ τ C : ℝ} (L : Side) {T : Tile (Biglot I) r} (h : τ ≤ L.val*σ) (he : 0≤τ) (hx : Bail (fame _) σ T C) :
    Bail (fame _) τ (jetty (scroll L I).symm T) (Real.exp (8*τ)*C) := by
   refine ⟨mul_nonneg (Real.exp_pos _).le hx.1,fun i a=>?_⟩
   let f : Gorge.pack i a→ Gorge.pack i ((scroll L I).symm a):= fun u=> ⟨(scroll L I).symm ∘ u.val,congr_arg (scroll L I).symm u.property⟩
   rw [ENNReal.ofReal_mul (Real.exp_pos _).le]; refine le_trans ?_ (mul_le_mul_right (hx.watch f (fun v w hv=>Subtype.ext (funext fun j=>(scroll L I).symm.injective (congr_fun (congr_arg Subtype.val hv) j)))) _); rw [←ENNReal.tsum_mul_left]
   refine ENNReal.tsum_le_tsum fun v=>?_;unfold glitter jetty;exact (mul_le_mul_left (shift_wide L v.val h he) _).trans_eq (mul_assoc ..)
end YM.FormalBulk08.Bank
