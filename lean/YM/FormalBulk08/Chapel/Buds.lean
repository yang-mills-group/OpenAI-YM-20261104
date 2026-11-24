import YM.FormalBulk08.Chapel.Hands

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Chapel
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries Next.Free RG Precision
open Lotus Shore Mesa Gorge City Cork Rift Lava
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge}{σ η C : ℝ}{m r:ℕ}{L : Side}{I J : Type}

def Par {A: Type}[Fintype A] (f : Wand A→ℝ):= ∃ N:ℕ,∃ C:ℝ,0≤C ∧ ∀ w, ‖f w‖ ≤ C*(1+size w)^N
variable {A: Type}[Fintype A]
lemma par_add {f g: Wand A→ℝ}(h:Par f)(e:Par g): Par (f+g):= by
   obtain ⟨m,x,hx,h⟩:=h; obtain ⟨n,y,hy,e⟩:=e; refine ⟨m+n,x+y,add_nonneg hx hy, fun i=> (norm_add_le ..).trans ((add_le_add (h i) (e i)).trans ?_)⟩;rw [add_mul]; gcongr <;> simp
lemma par_mul {f g: Wand A→ℝ}(h:Par f)(e:Par g): Par (f*g):= by
   obtain ⟨m,x,hx,h⟩:=h; obtain ⟨n,y,hy,e⟩:=e; refine ⟨m+n,x*y,mul_nonneg hx hy,fun i=>?_⟩; rw [Pi.mul_apply,norm_mul,pow_add,mul_mul_mul_comm];exact mul_le_mul (h i) (e i) (norm_nonneg _) (by positivity)
lemma par_shift {f:Wand A→ℝ}(h:Par f)(x : Wand A): Par (fun i=> f (i+x)) := by
    obtain ⟨m,V,hv,h⟩:=h; refine ⟨m,V*(1+size x)^m,by positivity,fun w=>(h _).trans ?_⟩; rw [mul_assoc,←mul_pow]; gcongr; have ht : (size (w+x):ℝ)≤size w+size x:=by exact_mod_cast size_add w x
    nlinarith only [ht,mul_nonneg (Nat.cast_nonneg (α:=ℝ) (size w)) (Nat.cast_nonneg (size x))]
lemma par_still (q:ℝ): Par (fun _ : Wand A=>q):= ⟨0,‖q‖,norm_nonneg _,fun w=>by simp⟩

def curveW (i:A)(w:Wand A):ℝ:= w i
lemma par_curve (i:A):Par (curveW i):= by
    refine ⟨1,1,zero_le_one,fun w=>?_⟩; have he : ‖curveW i w‖≤ (size w:ℝ):= by rw [curveW,Real.norm_eq_abs,← Int.cast_abs,← Int.natCast_natAbs]; exact_mod_cast (Finset.single_le_sum (f:=fun i:A=> (w i).natAbs) (fun _ _=> Nat.zero_le _) (Finset.mem_univ i))
    exact he.trans (by rw [pow_one,one_mul];linarith only)
lemma rise_hat (p:ℝ)(j:ℕ): Ring.choose p (j+1)= ((j:ℝ)+1)⁻¹*(Ring.choose p j * (p-j)) := by
   have h: j≤ j+1:=by omega
   rw [← Ring.choose_one_right (p-j)]; have he:= Ring.choose_smul_choose p h;rw [←Nat.choose_symm h,show j+1-j=1 by omega,Nat.choose_one_right,nsmul_eq_mul] at he; rw [←he]; push_cast; rw [inv_mul_cancel_left₀ (by positivity)]
lemma par_hat (t:Grades A): Par (hat t):= by
    have hu (i:A)(k:ℕ): Par (fun w:Wand A=>Ring.choose (w i:ℝ) k):=by
       induction k with
       | zero=> simp_rw [Ring.choose_zero_right]; exact par_still _
       | succ k h=> simp_rw [rise_hat _ k]; have ht : (fun w:Wand A=> (w i:ℝ)-(k:ℝ))=curveW i+(fun _ => -(k:ℝ)):= by ext; simp [curveW]; ring
                    exact par_mul (par_still _) (par_mul h (show Par (fun w=> ((w i:ℝ)-(k:ℝ))) from by rw [ht];exact par_add (par_curve _) (par_still _)))
    have ht (S:Finset A):Par (fun w:Wand A=> ∏ i∈S,Ring.choose (w i:ℝ) (t i)) := by
        induction S using Finset.induction with
        | empty=>simp_rw [Finset.prod_empty];apply par_still
        | @insert a s h ha=> simp_rw [Finset.prod_insert h];exact par_mul (hu a _) ha
    exact ht Finset.univ

lemma reptile (x:Cover)(t:chain I m): Injective (snake x t):= by
   intro u v h; ext ⟨i,j⟩; let b:= congr_arg Prod.fst (congr_fun h i); change x+rack u i=x+rack v i at b; exact congr_fun (add_left_cancel b) j
lemma serp (x:Biglot I) (t : chain I m) (w:cloud m): size w≤m*wide (fame I) (Fin.cons x (snake x.1 t w)):= by
    let U : chain (Biglot I) (m+1):=Fin.cons x (snake x.1 t w);rw [real_size]; refine le_trans (b:=∑ _i:Fin m,wide (fame I) U) ?_ (by simp [U]); refine Finset.sum_le_sum fun j _=>?_ ; refine le_trans (le_of_eq ?_) (reached (fame I) U j.succ 0); simp [fame,U,capD,snake]

def rowC (T:Tile (Biglot I) (m+1))(x:Biglot I)(t:chain I m)(w:cloud m):= T (Fin.cons x (snake x.1 t w))
lemma cost_rowC (x:Biglot I)(t:chain I m)(a:ℝ)(h : a*m≤σ)(hx: 0≤a)(T: Tile (Biglot I) (m+1))(hp : Bail (fame I) σ T C):
   (∑' w:cloud m,Gorge.shine a (size w)* ‖rowC T x t w‖ₑ) ≤ ENNReal.ofReal C := by
   let f : cloud m → pack (0:Fin (m+1)) x := fun w=>⟨Fin.cons x (snake x.1 t w),by simp⟩
   have hf : Injective f:= fun u v e=> reptile x.1 t (show _ from by simpa only [f,Fin.cons_inj,true_and] using! congr_arg Subtype.val e)
   refine le_trans ?_ (hp.watch f hf); apply ENNReal.tsum_le_tsum; intro v; unfold glitter; apply mul_le_mul_left; unfold Gorge.shine; apply ENNReal.ofReal_le_ofReal;apply Real.exp_monotone; refine le_trans (mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ)|>.mpr (serp x t v)) hx) ?_;push_cast;rw [←mul_assoc];exact mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)
lemma costs_rowC (hs:0<σ) {f : cloud m → ℝ}(h:Par f) (I: Type):∃ B:ℝ,0≤B ∧ ∀ C:ℝ,∀ (T: Tile (Biglot I) (m+1)) x t,Bail (fame I) σ T C→ (∑' w:cloud m,‖rowC T x t w*f w‖ₑ)≤ ENNReal.ofReal (B*C):= by
   let l:= σ/(m+1);have hl: 0<l:=by unfold l;positivity
   have he:l*m≤σ:= by calc
       _ ≤ l*(m+1):= by gcongr; simp
       _ = _:= div_mul_cancel₀ _ (by positivity)
   obtain ⟨k,X,hx,h⟩:=h;obtain ⟨B,hB,H⟩:=pockets k hl;have hV :0≤X*B:= mul_nonneg hx hB.le
   refine ⟨X*B,hV,fun V T x t hp=>?_⟩; rw [ENNReal.ofReal_mul hV]; refine le_trans ?_ (mul_le_mul_right (cost_rowC x t l he hl.le T hp) _); rw [←ENNReal.tsum_mul_left]; refine ENNReal.tsum_le_tsum fun w=>?_
   rw [enorm_mul,mul_comm ‖rowC T x t w‖ₑ,←mul_assoc]; apply mul_le_mul_left; unfold Gorge.shine;rw [←ENNReal.ofReal_mul hV,←ofReal_norm]; apply ENNReal.ofReal_le_ofReal; exact ((h w).trans (mul_le_mul_of_nonneg_left (H _ (Nat.cast_nonneg _)) hx)).trans_eq (mul_assoc ..).symm
lemma summableRow (hs : 0<σ){f:cloud m→ℝ}(h:Par f) {T:Tile (Biglot I) (m+1)} (H:Bail (fame I) σ T C) (x t): Summable (fun w=>rowC T x t w*f w):= by obtain ⟨B,hb,he⟩:= costs_rowC hs h I; exact (tsum_enorm_ne_top_iff_summable_norm.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (he C T x t H))).of_norm
end YM.FormalBulk08.Chapel
