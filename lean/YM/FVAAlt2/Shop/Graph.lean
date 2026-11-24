import YM.FVAAlt2.Shop.Button
/-! Equality through WEIGHT d at top inserted columns. `read_base`
 extended to all products, using width thickness. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Shop
open Lattice Function Finset Filter Topology Wilson Labels Source Source.Drops
open Comparison.Stencils.Corona (Crumb Primary Binds Tally demonstrates act_simple plated scape)
open MS MS.Koszul MS.Native MS.Landau MS.Landau.Detect MS.Plane MS.Tone MS.Theater MS.Book
open Next.Foundations
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{d k:ℕ}{A:Type}{p:Sector A}
local notation "Θ"=> Lane4 G
local notation "P"=> hands G
local infix:70 " ⋄ "=> product ( hands G )
local notation "Pr"=> PertExtension.Heat.Ray.print

structure Jewel (d:ℕ)(f g:ℝ→ℂ): Prop where
 one: ContDiff ℝ ∞ f
 two: ContDiff ℝ ∞ g
 same: ∀ i ≤ d, reading i f=reading i g
namespace Jewel
variable {f g f' g':ℝ→ℂ}
lemma refl (f:ℝ→ℂ)(h:ContDiff ℝ ∞ f): Jewel d f f:= ⟨h,h,fun _ _=>rfl⟩
lemma add (h:Jewel d f g)(h':Jewel d f' g'):Jewel d (f+f') (g+g'):= ⟨ h.one.add h'.one,h.two.add h'.two,fun i hi=>by simp only [Pi.add_def, read_add h.one h'.one,read_add h.two h'.two,h.same i hi,h'.same i hi]⟩
lemma mul (h:Jewel d f g)(h':Jewel d f' g'):Jewel d (f*f') (g*g'):= by
 refine ⟨ h.one.mul h'.one,h.two.mul h'.two,fun i hi=>?_⟩; rw [Pi.mul_def,Pi.mul_def,read_mul h.one h'.one,read_mul h.two h'.two]; apply sum_congr rfl; intro j hj; rw [h.same j (by simp at hj;omega),h'.same (i-j) (by omega)]
lemma scattered {f g:ℝ→Shared A ℂ}(w: Legs A)(h:∀ l r,Split l r w→ Jewel d (fun x=>f x l r) (fun x=>g x l r)): Jewel d (fun x=> scatter p w (f x)) (fun x=> scatter p w (g x)):=by
 induction w generalizing f g with
 | nil=> exact h [] [] .nil
 | cons i w ih=> exact ih (fun l r s=> (h _ _ s.left).add ((refl (fun _=>_) contDiff_const).mul (h _ _ s.right)))
lemma metered {f g f' g':ℝ→ Law G}(h:∀ w,Jewel d (fun x=>f x w) (fun x=>g x w))(h':∀ w,Jewel d (fun x=>f' x w) (fun x=>g' x w))(w:List Θ): Jewel d (fun x=> ( f x ⋄ f' x ) w) (fun x=> ( g x ⋄ g' x ) w):=by simp_rw [Koszul.scattered]; exact Jewel.scattered _ fun l r _=> (h l).mul (h' r)
end Jewel

def depths (t:ℝ)(w:List Θ):ℂ:= (w.map (fun x=> lensw x t)).prod
def glowm (t:ℝ)(w:List Θ):ℂ:= (t:ℂ)^w.length*depths t w
abbrev fromt (t:ℝ)(x:Θ):= hits x t

def shaped (t:ℝ) : Law G→ₗ[ℂ] Law G where
 toFun F w:= glowm t w * F (w.map (fromt t))
 map_add' _ _:= funext fun _=>mul_add ..
 map_smul' _ _:= funext fun _=>mul_left_comm ..
lemma carriedS (t:ℝ)(v x: Law G): shaped t (v⋄x)=shaped t v ⋄ shaped t x:= by
 funext w; change glowm t w*_= _; rw [scattered, Lifting.scatter_move _ (fromt (G:=G) t) (fun _=>rfl),scattered]
 let u:=allocate P w (R:=ℂ); change (glowm t w) • u _=_; rw [← map_smul u]; apply scatter_congr; intro a b ht
 have he: depths t a*depths t b=depths t w:=by simpa [depths] using ((split_perm ht).map (fun x=> lensw x t)).prod_eq
 change glowm t w*(v _*x _)= (glowm t a* v _)*(glowm t b*x _); unfold glowm; rw [← he,← split_length ht,pow_add]; ring
lemma shaped_c (t:ℝ)(p:ℂ): shaped t (coin (A:=Lane4 G) p) = coin p :=by funext w; rcases w with _|⟨i,w⟩; exact (by simp [shaped,glowm,depths]); exact mul_zero _

abbrev α (p:Primary G):= (Ψ G (Pict G p)).val
lemma cashΩ (v:ℂ):α (G:=G) (MvPolynomial.C v)=coin v:= by unfold α Pict Ψ; rw [MvPolynomial.aeval_C]; change (MvPolynomial.aeval (onevar (G:=G)) (MvPolynomial.C _)).val=_; rw [MvPolynomial.aeval_C]; exact Theater.cash1 _
lemma starting(x:Crumb G)(w:List Θ): Jewel d (fun t=> shaped t (α (MvPolynomial.X x)) w) (fun t=>targetK d (MvPolynomial.X x) t w):= by
 have hU(a:Θ)(t:ℝ): shaped t (α (MvPolynomial.X x)) [a]=(t:ℂ)^1 * (lensw a t * curlw (hits a t) x):= by change shaped _ (Ψ G _).val _=_; rw [Ωcurl]; unfold shaped; simp [glowm, depths,mono]; ring -- Λ
 unfold α; simp_rw [onbutton, Finset.sum_apply, Pi.smul_apply]; rcases w with _|⟨i,_|a,w⟩; pick_goal 2
 · simp_rw [hU i];
   let f(j:ℕ)(t:ℝ):=(t:ℂ)^(j+2) • mono ( RowLeg G j (offLeg x j)) [i]; let u(t:ℝ):= lensw i t * curlw ( hits i t ) x
   have hf(j:ℕ): ContDiff ℝ ∞ (f j):= registrSmooth _ _ contDiff_const -- h simp
   have hu: ContDiff ℝ ∞ u:= (lenswSmooth i).mul (ex_leg x i)
   refine ⟨registrSmooth 1 u hu, ContDiff.sum (fun j _=> hf j),?_⟩; intro k hk; change reading k (fun t:ℝ=> _ * u t)= reading k (fun t:ℝ=>∑ j∈Finset.range (d-1), f j t)
   rw [read_sum (fun j _=>hf j)]; unfold u f; simp_rw [ smul_eq_mul,pot_read, mono ]; cases k with
   | zero=>simp [reading]
   | succ k=> rw [add_comm k,registry _ 1 _ hu]; cases k with
     | zero=> rw [curl_cash]; exact (Finset.sum_eq_zero fun j _=> if_neg (by omega)).symm
     | succ k=> rw [curl_slot,Finset.sum_eq_single_of_mem k (by simp; omega),if_pos (by omega)]; intro b _ hb; exact if_neg (by omega)
 all_goals
   simp only [Ωcurl, shaped,LinearMap.coe_mk,AddHom.coe_mk,List.map_nil,List.map_cons,mono,mul_zero,smul_zero,Finset.sum_const_zero]
   exact Jewel.refl _ contDiff_const
lemma builds (p:Primary G) (w:List Θ): Jewel d (fun t=> shaped t (α p) w) (fun t=> targetK d p t w):=by
 induction p using MvPolynomial.induction_on generalizing w with
 | C q=>
   simp_rw [cashΩ,shaped_c]; have hh(t:ℝ): targetK d (G:=G) (MvPolynomial.C q) t=coin q:= by unfold targetK PertExtension.Heat.Ray.print age; simp [cus]; -- $ try
   simp_rw [hh]; exact Jewel.refl _ contDiff_const
 | add v u hv hu=> unfold α targetK; simp_rw [map_add,Submodule.coe_add, map_add,Pi.add_apply]; exact (hv w).add (hu w)
 | mul_X x i hx=>
   let u:= MvPolynomial.X i (R:=ℂ); have he(t:ℝ): shaped t (α (x*u))= shaped t (α x) ⋄ shaped t (α u) :=by unfold α; rw [map_mul,map_mul,darkM,carriedS]
   unfold u at he; simp_rw [he]; unfold targetK; simp_rw [map_mul,bags]; exact Jewel.metered hx (starting i) w
end YM.FVAAlt2.Shop
