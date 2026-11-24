import YM.FormalBulk08.Tundra.Lamp
import YM.FormalBulk08.Spruce.Fir

/-!
Per-letter MICRO buys subalong with exact link transfer. Thermal births only
for actual model. `Legibility` ANY suffices for unknown X not necessarily
incense: don't use σ(j) in this place.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Tundra
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Clover
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{K:KernelChoices}{E m n l e r j t d D R u:ℕ} {X I:Type}
variable {J U:X→ℕ}{F:∀ i:X, Flight (J i) (U i)}{V:∀ i:X,Lodge (F i).patch}{τ:Time X}{σ η δ g μ:X→ℝ}
variable {o:Loc G 1}{T S:X→ Anthem D G}{Z:Frame G d}{hL:∀ i,2≤(F i).L.val}
def Sugar (o:Loc G 1)(τ:Time X)(u:ℕ)(μ g:X→ℝ)(r:ℕ)(P Q:X→Studio D→Tile (edgeL G) r): Prop := ∃ B:X→ℝ,Soft τ B ∧ (∀ i,0≤B i) ∧ ∀ x A,0≤A→ (∀ p: Studio D, Knoxville (_root_.YM.FormalBulk08.Sable.grain (fame _) 1) u (0,o) (P x p) (A*‖p‖)) → ∀ p, Knoxville (_root_.YM.FormalBulk08.Sable.grain (fame _) 1) u (0,o) (Q x p) ((μ x*A+B x*g x)*‖p‖)
-- don't require a real scalar pay if coefficient enters only as Toe.
structure Ticket (K:KernelChoices)(Z:Frame G d)(o:Loc G 1)(F:∀ i:X,Flight (J i) (U i))(V:∀ i:X,Lodge (F i).patch)(E R D u:ℕ)(τ:Time X)(μ:X→ℝ):Prop where
   ample:d*d ≤ u
   bills : ∀ e≤ E,∀ r≤R+E,∀ l≤R,∃ C:X→ℝ, Soft τ C ∧ ∀ i, OfficeK K Z o u (F i) (V i) e r l D (μ i) (C i)
structure Reachable (d r e u:ℕ) (F:∀ i:X,Flight (J i) (U i))(V:∀ i:X,Lodge (F i).patch)(K:KernelChoices)(L:∀ i,2≤(F i).L.val) (o:Loc G 1)(τ:Time X)(g:X→ℝ)(T S:X→Anthem D G):Prop where
    mark: Sigh u τ o g (fun i p=> S i p e r- Grail.blade (F i) K (V i) (T i) d e r (L i) p)
    onward: ∀ j k, precede e r j k→ Wayfarer S j k u τ o g
lemma tilted {T:X→ Studio D→ Tile (edgeL G) r}(i:Letter Z)(ht: Sigh u τ o g T)(hp:d*d≤u): Faint τ g (fun x=>pearlJ Z (T x (inside Z i D)) (mint Z i)):= by
   obtain ⟨B,b,v,H⟩:=ht; obtain ⟨C,c,h⟩:=rent_book Z i o r hp; refine ⟨_, ((soft_coin _ C).times b).times (soft_coin τ ‖inside Z i D‖),fun i=>mul_nonneg (mul_nonneg c (v i)) (norm_nonneg _),fun x=>?_⟩; refine (h _ _ (H x (inside Z i D))).trans_eq ?_;ring
lemma crease_cover (Z:Frame G d)(h:∀ x,Clef o (T x) l)(hw:∀ j:Letter Z,Faint τ g (fun i=>coeff e (echo Z (T i) j)))(hp:∀ k m:ℕ,k<e→m≤l+k → Wayfarer T k m u τ o g)(hs:∀ x, 0≤g x):
   ∃ B:X→ℝ, Soft τ B ∧(∀ i,0≤ B i) ∧ (∀ i,Pawn o u (T i) e (B i*g i)) ∧∀ i: Letter Z,∀ j, ‖coeff e (echo Z (T j) i)‖≤ B j*g j:= by
    let U:= (Finset.range e ×ˢ Finset.range (l+e+1)).filter (fun i=> i.2 ≤ l+i.1)
    choose! B hB b HB using fun i:↥U=> hp i.val.1 i.val.2 (Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_filter.mp i.property).1).1) (Finset.mem_filter.mp i.property).2
    let C (x:X):= ∑ w,B w x; have hc i:0≤C i:= Finset.sum_nonneg (fun j _=> b j i)
    obtain ⟨A,a,W,Q⟩:= bill_many hs Finset.univ (fun j _=>hw j)
    have hv i:0≤C i+A i:= add_nonneg (hc i) (W i); refine ⟨_, (soft_bill _ (fun w _=>hB w)).plus a,hv,fun i=>?_,fun i k=>?_⟩
    · have ht:=mul_nonneg (hv i) (hs i);refine ⟨ht,fun j hj m p=>?_⟩; by_cases he:m≤l+j
      · let y: ↥U:=⟨(j,m),by simp [U];omega⟩; have hx:B y i ≤C i:=Finset.single_le_sum (fun j _=> b j i) (Finset.mem_univ y); exact (HB y i p).mono (by change _ ≤ (C i+A i)*g i *‖p‖;rw [mul_assoc];exact mul_le_mul_of_nonneg_right (hx.trans (le_add_of_nonneg_right (W i))) (mul_nonneg (hs _) (norm_nonneg _)))
      rw [show T i p j m=0 from Classical.byContradiction fun ht=> he ((h i).fare.1 p j m ht)]; exact (Knox_zeros _).mono (mul_nonneg ht (norm_nonneg _))
    rw [add_mul]; exact (Q i (Finset.mem_univ _) k).trans (le_add_of_nonneg_left (mul_nonneg (hc k) (hs k)))
lemma vapor (w:Ticket K Z o F V E R D u τ μ)(h: Reachable d r e u F V K hL o τ g T S)(hx:∀ j k:ℕ,precede e r j k → Wayfarer T j k u τ o g)(hE:e≤E)(hr:r≤R+E)(hv:∀ i,Clef o (T i) l)(hp:l≤R)(hP:∀ j,Faint τ g (fun i=>coeff e (echo Z (T i) j)))(hg:∀ x,0≤g x): Sugar o τ u μ g r (fun x p=> T x p e r) (fun x p=> S x p e r):= by
    obtain ⟨A,hA,H,ht,Q⟩:= crease_cover Z hv hP (fun j m hj _=>hx j m (Or.inl hj)) hg; obtain ⟨C,hC,W⟩:=w.bills e hE r hr l hp; obtain ⟨B,b,hB,Hb⟩:=h.mark
    refine ⟨_,(hC.radius.times hA).plus b,fun i=>add_nonneg (mul_nonneg (abs_nonneg _) (H i)) (hB i),fun x A' ha Hx p=>?_⟩
    have hv:= (Hb x p).add ((W x).claim (T x) (hv x) _ (ht x) (fun i=>Q i x) A' ha Hx (hL x)|>.2 p); rw [sub_add_cancel] at hv;apply hv.mono;apply (add_le_add_right (mul_le_mul_of_nonneg_right (add_le_add_right (mul_le_mul_of_nonneg_right (le_abs_self (C x)) (mul_nonneg (H x) (hg x))) _) (norm_nonneg p)) _).trans_eq;ring
lemma vocals (i:Letter Z)(w:Ticket K Z o F V E R D u τ μ)(h: Reachable d r e u F V K hL o τ g T S)(hx:∀ j k:ℕ,precede e r j k→Wayfarer T j k u τ o g)(hE:e≤E)(hr:r≤R+E)(hv:∀ i,Clef o (T i) l)(hp:l≤R)(hP:∀ j,Faint τ g (fun i=> coeff e (echo Z (T i) j)))(hg:∀ x,0≤g x)(hj:slots Z i=r): Faint τ g (fun x=> pearlJ Z (S x (inside Z i D) e r) (mint Z i)):= by
    let X1 i p:= Grail.blade (F i) K (V i) (T i) d e r (hL i) p;let Y i p:= S i p e r-X1 i p; have hh:Faint τ g (fun x=> pearlJ Z (Y x (inside Z i D)) (mint Z i)):= tilted i h.mark w.ample
    obtain ⟨A,hA,H,ht,Q⟩:= crease_cover Z hv hP (fun j m hj _=>hx j m (Or.inl hj)) hg; obtain ⟨C,hC,Hc⟩:=w.bills e hE r hr l hp
    choose σ Z' hs hz hσ using fun x=>(hv x).fare.2.2 e r
    let B x:=sack u (σ x)* Z' x; have hB x:0≤B x:=mul_nonneg (sack_pos _ (hs x)) (hz x)
    have hy x:= (Hc x).claim (T x) (hv x) _ (ht x) (fun i=>Q i x) (B x) (hB x) (fun p=> by simpa only [B,mul_assoc] using sack_to u (hs x) le_rfl (hσ x p)) (hL x)
    have hr:Faint τ g (fun x=> pearlJ Z (X1 x (inside Z i D)) (mint Z i)):=by
       refine ⟨_,hC.radius.times hA,fun x=>mul_nonneg (abs_nonneg _) (H _),fun x=>?_⟩; rw [mul_assoc]; exact ((hy x).1 i hj).trans (mul_le_mul_of_nonneg_right (le_abs_self (C x)) (mul_nonneg (H x) (hg x)))
    obtain ⟨B,b,hB,H⟩:=h.mark; refine (hh.plus hr).lower (fun x=> le_of_eq ?_); have ht:= runners_chalk Z o (Y x (inside Z i D)) (X1 x (inside Z i D)) (H x _) ((hy x).2 _) (mint Z i) ((Nat.mul_le_mul_left d (slotsFits Z i)).trans w.ample); rw [show Y x _+X1 x _=_ from sub_add_cancel ..] at ht; rw [ht]
lemma loser (i:Letter Z)(hs:d*d≤u)(h:∀ j, j<e→∀ k,Wayfarer S j k u τ o g)(hv:Faint τ g (fun x=>pearlJ Z (S x (inside Z i D) e (slots Z i)) (mint Z i))) : Faint τ g (fun x=>coeff e (echo Z (S x) i)):= by
    simp_rw [echoline];apply faint_sums _;intro r hr;let k:=Pose.slots Z i;by_cases hz :slots Z i-r≤e; swap
    · simp_rw [if_neg hz];apply faint_zero
    simp_rw [if_pos hz];by_cases hx:r=k
    · subst r;unfold k; rw [Nat.sub_self,Nat.sub_zero];exact hv
    have he:r<slots Z i:=by rw [Finset.mem_range] at hr; unfold k at hx;omega
    exact tilted (T:=fun x p=>S x p (e-(Pose.slots Z i-r)) r) i (h (e-(Pose.slots Z i-r)) (by omega) _) hs
lemma loss (w:Ticket K Z o F V E R D u τ μ)(h: Reachable d r e u F V K hL o τ g T S)(hx:∀ j k:ℕ,precede e r j k→Wayfarer T j k u τ o g)(hE:e≤E)(hr:r≤R+E)(hv:∀ i,Clef o (T i) l)(hp:l≤R)(hP:∀ j,Faint τ g (fun i=>coeff e (echo Z (T i) j)))(hg:∀ x,0≤g x) (j)(i:Letter Z)(he:j<e ∨ j=e∧r ≤ slots Z i): Faint τ g (fun x=>coeff j (echo Z (S x) i)):= by
    obtain hh|⟨hh,hy⟩:= he
    · exact loser (S:=S) i w.ample (fun k hk m=>h.onward k m (Or.inl (lt_trans hk hh))) (tilted (T:=fun x p=>S x p j (Pose.slots Z i)) i (h.onward j (Pose.slots Z i) (Or.inl hh)) w.ample)
    rw [hh]; apply loser (S:=S) i w.ample (fun k hk m=>h.onward k m (Or.inl hk)); rcases lt_or_eq_of_le hy with hy|hy
    · exact tilted (T:=fun x p=>S x p e (Pose.slots Z i)) i (h.onward e (Pose.slots Z i) (Or.inr ⟨rfl,hy⟩)) w.ample
    exact hy ▸ vocals i w h hx hE hr hv hp hP hg hy.symm
end YM.FormalBulk08.Tundra
