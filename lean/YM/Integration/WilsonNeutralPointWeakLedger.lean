import YM.Integration.WilsonNeutralPointWeakWick
import YM.FormalBulk08.Tundra.Feel
import YM.FormalBulk08.Spruce.Fir

/-!
Per-letter MICRO buys subalong with exact link transfer. Thermal births only
for actual model. `Legibility` ANY suffices for unknown X not necessarily
incense: don't use σ(j) in this place.
-/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonNeutralPointWeakLedger
open FormalBulk08 Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Clover
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open WilsonNeutralPointSalary WilsonNeutralPointWeakWick Tundra
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{K:KernelChoices}{E m n l e r j t d D R u:ℕ} {X I:Type}
variable {J U:X→ℕ}{F:∀ i:X, Flight (J i) (U i)}{V:∀ i:X,Lodge (F i).patch}{τ:Time X}{σ η δ g μ:X→ℝ}
variable {o:Loc G 1}{T S:X→ Anthem D G}{Z:Frame G d}{hL:∀ i,2≤(F i).L.val}
structure Admission (K:KernelChoices)(Z:Frame G d)(o:Loc G 1)(u:ℕ)(P:Flight j t)
    (V:Lodge P.patch)(x:Site P.L)(e r l D:ℕ)(μ b:ℝ):Prop where
  claim : ∀ T:Anthem D G,Clef o T l→∀ B:ℝ,Pawn o u T e B→
    (∀v,‖coeff e (echo Z T v)‖≤B)→∀ A:ℝ,0≤A→
    (∀p,Knoxville (grain (fame _) 1) u (0,o) (T p e r) (A*‖p‖))→∀hL:2≤P.L.val,
    (∀v,Pose.slots Z v=r→‖pearlJ Z (land P K V T d e r x hL (inside Z v D)) (mint Z v)‖≤b*B) ∧
    ∀p,Knoxville (grain (fame _) 1) u (0,o) (land P K V T d e r x hL p) ((μ*A+b*B)*‖p‖)

structure Ledger (K:KernelChoices)(Z:Frame G d)(o:Loc G 1)(F:∀i:X,Flight (J i) (U i))
    (V:∀i,Lodge (F i).patch)(x:∀i,Site (F i).L)(E R D u:ℕ)(τ:Time X)(μ:X→ℝ):Prop where
  ample : d*d≤u
  bills : ∀ e≤E,∀ r≤R+E,∀ l≤R,∃ C:X→ℝ,Soft τ C∧∀i,Admission K Z o u (F i) (V i) (x i) e r l D (μ i) (C i)

structure Resolved (d r e u:ℕ)(F:∀i:X,Flight (J i) (U i))(V:∀i,Lodge (F i).patch)
    (K:KernelChoices)(hL:∀i,2≤(F i).L.val)(x:∀i,Site (F i).L)(o:Loc G 1)(τ:Time X)(g:X→ℝ)
    (T S:X→Anthem D G):Prop where
  mark : Sigh u τ o g (fun i p=>S i p e r-land (F i) K (V i) (T i) d e r (x i) (hL i) p)
  onward : ∀j k,precede e r j k→Wayfarer S j k u τ o g

variable {x:∀i,Site (F i).L}
theorem diagonal (w:Ledger K Z o F V x E R D u τ μ)(h: Resolved d r e u F V K hL x o τ g T S)(hx:∀ j k:ℕ,precede e r j k → Wayfarer T j k u τ o g)(hE:e≤E)(hr:r≤R+E)(hv:∀ i,Clef o (T i) l)(hp:l≤R)(hP:∀ j,Faint τ g (fun i=>coeff e (echo Z (T i) j)))(hg:∀ x,0≤g x): Sugar o τ u μ g r (fun x p=> T x p e r) (fun x p=> S x p e r):= by
    obtain ⟨A,hA,H,ht,Q⟩:= crease_cover Z hv hP (fun j m hj _=>hx j m (Or.inl hj)) hg; obtain ⟨C,hC,W⟩:=w.bills e hE r hr l hp; obtain ⟨B,b,hB,Hb⟩:=h.mark
    refine ⟨_,(hC.radius.times hA).plus b,fun i=>add_nonneg (mul_nonneg (abs_nonneg _) (H i)) (hB i),fun x A' ha Hx p=>?_⟩
    have hv:= (Hb x p).add ((W x).claim (T x) (hv x) _ (ht x) (fun i=>Q i x) A' ha Hx (hL x)|>.2 p); rw [sub_add_cancel] at hv;apply hv.mono;apply (add_le_add_right (mul_le_mul_of_nonneg_right (add_le_add_right (mul_le_mul_of_nonneg_right (le_abs_self (C x)) (mul_nonneg (H x) (hg x))) _) (norm_nonneg p)) _).trans_eq;ring
theorem current (i:Letter Z)(w:Ledger K Z o F V x E R D u τ μ)(h: Resolved d r e u F V K hL x o τ g T S)(hx:∀ j k:ℕ,precede e r j k→Wayfarer T j k u τ o g)(hE:e≤E)(hr:r≤R+E)(hv:∀ i,Clef o (T i) l)(hp:l≤R)(hP:∀ j,Faint τ g (fun i=> coeff e (echo Z (T i) j)))(hg:∀ x,0≤g x)(hj:slots Z i=r): Faint τ g (fun x=> pearlJ Z (S x (inside Z i D) e r) (mint Z i)):= by
    let X1 i p:=land (F i) K (V i) (T i) d e r (x i) (hL i) p;let Y i p:= S i p e r-X1 i p; have hh:Faint τ g (fun x=> pearlJ Z (Y x (inside Z i D)) (mint Z i)):= tilted i h.mark w.ample
    obtain ⟨A,hA,H,ht,Q⟩:= crease_cover Z hv hP (fun j m hj _=>hx j m (Or.inl hj)) hg; obtain ⟨C,hC,Hc⟩:=w.bills e hE r hr l hp
    choose σ Z' hs hz hσ using fun x=>(hv x).fare.2.2 e r
    let B x:=sack u (σ x)* Z' x; have hB x:0≤B x:=mul_nonneg (sack_pos _ (hs x)) (hz x)
    have hy x:= (Hc x).claim (T x) (hv x) _ (ht x) (fun i=>Q i x) (B x) (hB x) (fun p=> by simpa only [B,mul_assoc] using sack_to u (hs x) le_rfl (hσ x p)) (hL x)
    have hr:Faint τ g (fun x=> pearlJ Z (X1 x (inside Z i D)) (mint Z i)):=by
       refine ⟨_,hC.radius.times hA,fun x=>mul_nonneg (abs_nonneg _) (H _),fun x=>?_⟩; rw [mul_assoc]; exact ((hy x).1 i hj).trans (mul_le_mul_of_nonneg_right (le_abs_self (C x)) (mul_nonneg (H x) (hg x)))
    obtain ⟨B,b,hB,H⟩:=h.mark; refine (hh.plus hr).lower (fun x=> le_of_eq ?_); have ht:= runners_chalk Z o (Y x (inside Z i D)) (X1 x (inside Z i D)) (H x _) ((hy x).2 _) (mint Z i) ((Nat.mul_le_mul_left d (slotsFits Z i)).trans w.ample); rw [show Y x _+X1 x _=_ from sub_add_cancel ..] at ht; rw [ht]

theorem projected (w:Ledger K Z o F V x E R D u τ μ)(h: Resolved d r e u F V K hL x o τ g T S)(hx:∀ j k:ℕ,precede e r j k→Wayfarer T j k u τ o g)(hE:e≤E)(hr:r≤R+E)(hv:∀ i,Clef o (T i) l)(hp:l≤R)(hP:∀ j,Faint τ g (fun i=>coeff e (echo Z (T i) j)))(hg:∀ x,0≤g x) (j)(i:Letter Z)(he:j<e ∨ j=e∧r ≤ slots Z i): Faint τ g (fun x=>coeff j (echo Z (S x) i)):= by
    obtain hh|⟨hh,hy⟩:= he
    · exact loser (S:=S) i w.ample (fun k hk m=>h.onward k m (Or.inl (lt_trans hk hh))) (tilted (T:=fun x p=>S x p j (Pose.slots Z i)) i (h.onward j (Pose.slots Z i) (Or.inl hh)) w.ample)
    rw [hh]; apply loser (S:=S) i w.ample (fun k hk m=>h.onward k m (Or.inl hk)); rcases lt_or_eq_of_le hy with hy|hy
    · exact tilted (T:=fun x p=>S x p e (Pose.slots Z i)) i (h.onward e (Pose.slots Z i) (Or.inr ⟨rfl,hy⟩)) w.ample
    exact hy ▸ current i w h hx hE hr hv hp hP hg hy.symm

private theorem shared {T:X→Studio D→Tile (edgeL G) r} (h:Sigh u τ o g T):
    Blizzard u τ o δ g T T:=by
  refine ⟨h,h,?_⟩
  simp_rw [sub_self]
  exact bear_void ..

theorem heard {Z':∀i,Train (J i)}{H':∀i,(F i).patch.Branches K G}{W:X→Pot G}
    {ρ:ChartRatio G}{a:hue G}
    (w:Wells τ F V H' ρ a σ η δ Z' Z' W W E)(h:Soft τ (fun i=>(η i)⁻¹))
    (hg:∀i,0≤g i)(hL:∀i,2≤(F i).L.val)(digit:∀i,Site (F i).L)
    (he:e≤E)(hU:∀j k,precede e r j k→Wayfarer T j k u τ o g)(d k:ℕ):
    Resolved d r e u (graded F Z') V K hL digit o τ g T
      (fun i=> WilsonNeutralPointMatrix.child (graded F Z' i) (V i) (W i) a ρ (H' i) (hL i) d k (digit i) (T i)):=by
  constructor
  · simp_rw [recorded,add_sub_cancel_left]
    exact (settled w h hL hg digit he (fun j m prev=>shared (hU j m prev)) d k).1
  · intro j m prev
    change Sigh u τ o g (fun i p=>WilsonNeutralPointMatrix.child (graded F Z' i) (V i) (W i) a ρ (H' i) (hL i) d k (digit i) (T i) p j m)
    simp_rw [recorded]
    apply Bear.plus (linear w h hL hg digit (shared (hU j m prev)) d).1
    exact (settled w h hL hg digit (by unfold precede at prev;omega)
      (fun j' m' hl=>shared (hU j' m' (by unfold precede at *;omega))) d k).1

end YM.Integration.WilsonNeutralPointWeakLedger
