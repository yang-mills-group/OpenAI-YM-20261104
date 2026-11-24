import YM.FVA2.Lambda.Kick
/-!
# WWW B₁(q,r,p) above (off-shell arbitrary)
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda.Slice
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Color MS.Native
open MS.Book MS.Book.Convolve MS.Dock MS.Train MS.Pearl MS.Emit MS.Garment MS.Garment.Wick MS.Plane.Wire
open MS.Arc MS.Rock MS.Rock.Path MS.Motif MS.Hem MS.Hem.Mell MS.Outlook MS.Halo MS.Alps MS.City
open Complex (I)
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}{n:ℕ}
local notation "Ψ"=>field (parity (C:=G.ColorIndex) (A:=Arts.L n))
abbrev EM (v:Arts.L n)(i:G.ColorIndex)(p:SectorP n): Shore G n:= (at_g v i,p)
variable (a b v w x:Arts.L n)(i j k:G.ColorIndex)(p q r:SectorP n)
lemma twice (f h:Rack G n)(hf:Book.rank 1 f)
    (a b c:Shore G n)(ha:Ψ a=false)(hb:Ψ b=false)(hc:Ψ c=false):
    bite n G f h [a,b,c]=f [a]*h [b,c]+f [b]*h [a,c]+f [c]*h [a,b]:= by
    rw [bite,scattered]; simp [scatter_cons,hf [a,b] (by norm_num),hf [b,c] (by norm_num),hf [a,c] (by norm_num),hf [] (by norm_num),hf [a,b,c] (by norm_num),ha,hb,hc]; abel
lemma foot : quill a b i [ EM w j q, EM x k r ]= ( ( if w=a then if x=b then rune j k i else 0 else 0 ) - ( if x=a then if w=b then rune j k i else 0 else 0 ) ):= by
    unfold quill; simp only [chew,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]; simp_rw [ pairv (F:=Motif.A n G a _) (H:=Motif.A n G b _) ( mon_leaf _ ) ( mon_leaf _ ) ]; simp [ Motif.A,lip,Motif.leaf,node1,at_g,onX,EM, field, cross,mul_add,mul_ite, Finset.sum_add_distrib ] -- simp collapses inside cond?
    simp [ite_and]; rw [r_ortho k j i]; split_ifs <;> ring
lemma rightR (a b:Arts.L n)(i:G.ColorIndex): Pure Ψ false (F₀ a b i):= ( show Mood false ( F₀ a b:Mield G n ) from (( realA b ).moment (δ a)).sub ((realA a).moment (δ b) ) ).tune i
lemma all_heads (l:Chan G n): Motif.leaf (onX true l) [ EM a i p ]=0:= by rcases l with ⟨_|l,c⟩ <;> simp [Motif.leaf,onX,EM,at_g,node1]
lemma march : cape (blazeV G n) [EM v i p,EM w j q,EM x k r]=0:= by unfold cape; simp only [Finset.sum_apply,Pi.smul_apply]; apply Finset.sum_eq_zero; intro l _; rw [ twice _ _ (mon_leaf (onX true l)) _ _ _ rfl rfl rfl,all_heads,all_heads,all_heads]; simp
lemma tstep : (∑ a:Arts.L n,∑ b:Arts.L n,∑ l:G.ColorIndex, F₀ a b l [EM v i p] * quill a b l [EM w j q,EM x k r])=2*I*rune j k i*(↑( Landau.delta x v (p w)- Landau.delta w v (p x)):ℂ):= by
    simp_rw [ EM, f_ref,ite_mul ]; simp only [zero_mul, Finset.sum_ite_eq,Finset.mem_univ, ↓reduceIte]; -- L
    change (∑ a:Arts.L n,∑ b:Arts.L n, (I*( ( Landau.delta b v (p a)- Landau.delta a v (p b):ℝ):ℂ))* quill a b i [ EM w j q,EM x k r ])=_; simp_rw [foot, mul_sub _ ((ite _ _ _):ℂ) (ite _ _ _), Finset.sum_sub_distrib, mul_ite, mul_zero ]; -- want ite nested; rw sum if out cond a independent
    simp; ring -- collapse sums
    -- fix
lemma carry (v w x:Arts.L n)(i j k:G.ColorIndex)(p q r: SectorP n): B₁ G n [ EM v i p, EM w j q, EM x k r ]= I*rune i j k * ( ( Landau.delta w v ((p-q) x)+ Landau.delta x w ((q-r) v)+ Landau.delta v x ((r-p) w):ℝ):ℂ):= by
    have he(a b:Arts.L n)(i:G.ColorIndex): bite n G (quill a b i) ( F₀ a b i )= bite n G ( F₀ a b i ) (quill a b i):= by obtain hp:= ( rightR a b i ).times_comm (show Pure Ψ false (quill a b i) from ((realA a).jawn (realA b) ).tune i); simp only [cross_false, one_smul] at hp; exact hp.symm
    rw [ B₁,Pi.add_apply, march,add_zero ]; unfold top3; simp only [Pi.smul_apply,Finset.sum_apply,Pi.add_apply,sume,he,smul_eq_mul]; simp_rw [ twice _ _ (rank_α _ _ _) (EM v i p) (EM w j q) (EM x k r) rfl rfl rfl ]; simp only [Finset.sum_add_distrib, tstep ]; push_cast; -- commute δ.P
    have h (a b:Arts.L n)(u t:ℝ): Landau.delta a b (u-t)= Landau.delta a b u- Landau.delta a b t:= by unfold Landau.delta; split <;> simp
    simp only [Pi.sub_apply,h, Complex.ofReal_sub]; -- inspect
    have D(a b:Arts.L n)(p:ℝ): Landau.delta a b p= Landau.delta b a p:= by unfold Landau.delta; split <;> split <;> simp_all
    rw [r_ortho i k j, r_clock k i j,← r_clock i j k, D v w (q x),D x v (p w), D w x (r v) ]; ring
-- remove place if compile
open Canvas (triple)
def rib (a b c:Axis)(p q r:QP):ℝ:= Slice.delta a b*((p-q) c) + Slice.delta b c*((q-r) a)+ Slice.delta c a*((r-p) b)
lemma t_WWW (a b c:Axis)(p q r:QP): triple G [W a i p,W b j q,W c k r]= I*rune i j k*(rib a b c p q r:ℂ):= by
    unfold triple; rw [pulse1]; obtain hx:= carry (n:=0) a b c i j k p q r; refine hx.trans ?_; have he(u v:Axis)(t:ℝ): Landau.delta u v t=Slice.delta v u*t:= by unfold Landau.delta Slice.delta; split <;> split <;> simp_all
    rw [ he,he,he ]; rfl
end YM.FVA2.Lambda.Slice
